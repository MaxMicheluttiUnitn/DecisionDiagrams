"""theory SDD module"""

import time
import re
from array import array
from typing import List, Set
import pydot
from pysmt.fnode import FNode
from pysdd.sdd import SddManager, Vtree, WmcManager, SddNode
from string_generator import SDDSequentailStringGenerator
from formula import get_atoms
from walker_sdd import SDDWalker
from utils import get_string_from_atom as _get_string_from_atom

def compute_sdd(phi: FNode,
                vtree_type: str = None,
                output_file: str = None,
                vtree_output: str = None,
                dump_abstraction: bool = False,
                print_mapping: bool = False,
                count_models: bool = False,
                count_nodes: bool = False,
                count_vertices: bool = False,
                qvars: List[FNode] = [],
                computation_logger: any = {}) -> None:
    ' ' 'Computes the SDD for the boolean formula phi and saves it on a file' ' '
    # Setting default values
    if vtree_type is None:
        vtree_type = "right"
    # if output_file is None:
    #     output_file = "output/sdd.dot"

    # BUILDING V-TREE
    start_time = time.time()
    print("Building V-Tree...")
    atoms = get_atoms(phi)
    var_count = len(atoms)
    string_generator = SDDSequentailStringGenerator()
    name_to_atom_map = {}
    for atom in atoms:
        name_to_atom_map[string_generator.next_string().upper()] = atom
    # print(name_to_atom_map)
    # for now just use appearance order in phi
    var_order = list(range(1, var_count + 1))
    vtree = Vtree(var_count, var_order, vtree_type)
    elapsed_time = time.time()-start_time
    print("V-Tree built in ", elapsed_time, " seconds")
    computation_logger["SDD"]["V-Tree building time"] = elapsed_time

    # SAVING VTREE
    if not vtree_output is None:
        start_time = time.time()
        print("Saving V-Tree...")
        if _save_sdd_object(vtree, vtree_output, name_to_atom_map, 'VTree'):
            elapsed_time = time.time()-start_time
            print("V-Tree saved as "+vtree_output+" in ",
                  elapsed_time, " seconds")
            computation_logger["SDD"]["V-Tree dumping time"] = elapsed_time
        else:
            print("V-Tree could not be saved: The file format of ",
                  vtree_output, " is not supported")

    # BUILDING SDD WITH WALKER
    start_time = time.time()
    print("Building SDD...")
    manager = SddManager.from_vtree(vtree)
    sdd_literals = [manager.literal(i) for i in range(1, var_count + 1)]
    atom_literal_map = dict(zip(atoms, sdd_literals))
    walker = SDDWalker(atom_literal_map, manager)
    sdd_formula = walker.walk(phi)
    elapsed_time = time.time()-start_time
    print("SDD built in ", elapsed_time, " seconds")
    computation_logger["SDD"]["DD building time"] = elapsed_time

    # QUANTIFYING OVER FRESH T-ATOMS
    start_time = time.time()
    print("Quantifying over fresh T-atoms...")
    existential_map = [0]
    for smt_atom in atom_literal_map.keys():
        if smt_atom in qvars:
            existential_map.append(1)
        else:
            existential_map.append(0)
    sdd_formula = manager.exists_multiple(
        array('i', existential_map), sdd_formula)
    elapsed_time = time.time()-start_time
    print("Quantified over fresh T-atoms in ",
          elapsed_time, " seconds")
    computation_logger["SDD"]["fresh T-atoms quantification time"] = elapsed_time

    # COUNTING NODES
    if count_nodes:
        total_nodes = sdd_formula.count()
        computation_logger["SDD"]["DD nodes"] = total_nodes
        print("Nodes in SDD: ", total_nodes)

    # COUNTING VERTICES
    if count_vertices:
        if sdd_formula.is_true() or not sdd_formula.is_decision():
            computation_logger["SDD"]["DD vertices"] = 0
            print("Vertices in SDD: ", 0)
        else:
            elems = sdd_formula.elements()
            queue: List[SddNode] = []
            for elem in elems:
                queue.extend([elem[0],elem[1]])
            total_edges = len(elems)
            visited: Set[SddNode] = set()
            visited.add(sdd_formula)
            while len(queue) > 0:
                first = queue.pop(0)
                if first.is_decision():
                    total_edges += 1
                    if not first in visited:
                        elems = first.elements()
                        for elem in elems:
                            queue.extend([elem[0],elem[1]])
                            total_edges+=1
                    visited.add(first)
            computation_logger["SDD"]["DD vertices"] = total_edges
            print("Vertices in SDD: ", total_edges)

    # MODEL COUNTING
    if count_models:
        start_time = time.time()
        print("Counting models through the SDD...")
        wmc: WmcManager = sdd_formula.wmc(log_mode=False)
        w = wmc.propagate()/(2**len(qvars))
        print(f"Model count: {w}")
        computation_logger["SDD"]["model count"] = w
        elapsed_time = time.time()-start_time
        print("Models counted in ", elapsed_time, " seconds")
        computation_logger["SDD"]["model counting time"] = elapsed_time

    # SAVING SDD
    if not output_file is None:
        start_time = time.time()
        print("Saving SDD...")
        if print_mapping:
            print("Mapping:")
            print(name_to_atom_map)
        if _save_sdd_object(sdd_formula, output_file, name_to_atom_map, 'SDD', dump_abstraction):
            elapsed_time = time.time()-start_time
            print("SDD saved as "+output_file+" in ",
                  elapsed_time, " seconds")
            computation_logger["SDD"]["dumping time"] = elapsed_time
        else:
            print("SDD could not be saved: The file format of ",
                  output_file, " is not supported")


def _save_sdd_object(sdd_object, output_file: str, mapping: dict[str, FNode], kind: str, dump_abstraction=False) -> bool:
    '''saves an SDD object on a file'''
    dot_content = sdd_object.dot()
    if kind == 'VTree':
        dot_content = _translate_vtree_vars(dot_content, mapping)
    elif kind == 'SDD' and not dump_abstraction:
        dot_content = _translate_sdd_vars(dot_content, mapping)
    tokenized_output_file = output_file.split('.')
    if tokenized_output_file[len(tokenized_output_file)-1] == 'dot':
        with open(output_file, "w") as out:
            print(dot_content, file=out)
    elif tokenized_output_file[len(tokenized_output_file)-1] == 'svg':
        (graph,) = pydot.graph_from_dot_data(dot_content)
        graph.write_svg(output_file)
    else:
        return False
    return True


VTREE_LINE_REGEX = r'n[0-9]+ [\[]label="[A-Z]+",fontname='
VTREE_KEY_START_REGEX = r'[A-Z]+",fontname='
VTREE_KEY_END_REGEX = r'",fontname='
VTREE_REPLECE_REGEX = VTREE_KEY_START_REGEX


def _translate_vtree_vars(original_dot: str, mapping: dict[str, FNode]) -> str:
    '''translates variables in the dot representation 
    of the VTree into their original names in phi'''
    result = """"""
    original_dot = original_dot.replace('width=.25', 'width=.75')
    for line in original_dot.splitlines():
        found = re.search(VTREE_LINE_REGEX, line)
        if not found is None:
            key_start_location = re.search(VTREE_KEY_START_REGEX, line).start()
            key_end_location = re.search(VTREE_KEY_END_REGEX, line).start()
            line = re.sub(VTREE_REPLECE_REGEX, _get_string_from_atom(
                mapping[line[key_start_location:key_end_location]])+"\",fontname=", line)
        result += line+"""
"""
    return result


SDD_LINE_LEFT_REGEX = r'[\[]label= "<L>(&not;)?([A-Z]+|[0-9]+)[|]<R>(&#8869;|&#8868;)?",'
SDD_LINE_RIGHT_REGEX = r'[\[]label= "<L>[|]<R>(&not;)?([A-Z]+|[0-9]+)",'
SDD_LINE_BOTH_REGEX = r'[\[]label= "<L>(&not;)?([A-Z]+|[0-9]+)[|]<R>(&not;)?([A-Z]+|[0-9]+)",'
SDD_KEY_START_LEFT_REGEX = r'([A-Z]+|[0-9]+)[|]'
SDD_KEY_END_LEFT_REGEX = r'[|]<R>'
SDD_KEY_START_RIGHT_REGEX = r'([A-Z]+|[0-9]+)",'
SDD_KEY_END_RIGHT_REGEX = r'",'
SDD_REPLACE_LEFT_REGEX = SDD_KEY_START_LEFT_REGEX
SDD_REPLACE_RIGHT_REGEX = SDD_KEY_START_RIGHT_REGEX


def _translate_sdd_vars(original_dot: str, mapping: dict[str, FNode]) -> str:
    '''translates variables in the dot representation of the SDD into their original names in phi'''
    result = """"""
    original_dot = original_dot.replace('fixedsize=true', 'fixedsize=false')
    for line in original_dot.splitlines():
        new_line = line
        # ONLY LEFT
        found = re.search(SDD_LINE_LEFT_REGEX, line)
        if not found is None:
            key_start_location = re.search(
                SDD_KEY_START_LEFT_REGEX, line).start()
            key_end_location = re.search(SDD_KEY_END_LEFT_REGEX, line).start()
            new_line = re.sub(SDD_REPLACE_LEFT_REGEX, _get_string_from_atom(
                mapping[line[key_start_location:key_end_location]])+"|", new_line)
        # ONLY RIGHT
        found = re.search(SDD_LINE_RIGHT_REGEX, line)
        if not found is None:
            key_start_location = re.search(
                SDD_KEY_START_RIGHT_REGEX, line).start()
            key_end_location = re.search(SDD_KEY_END_RIGHT_REGEX, line).start()
            new_line = re.sub(SDD_REPLACE_RIGHT_REGEX, _get_string_from_atom(
                mapping[line[key_start_location:key_end_location]])+"\",", new_line)
        # BOTH SIDES
        found = re.search(SDD_LINE_BOTH_REGEX, line)
        if not found is None:
            key_start_location = re.search(
                SDD_KEY_START_LEFT_REGEX, line).start()
            key_end_location = re.search(SDD_KEY_END_LEFT_REGEX, line).start()
            new_line = re.sub(SDD_REPLACE_LEFT_REGEX, _get_string_from_atom(
                mapping[line[key_start_location:key_end_location]])+"|", new_line)
            key_start_location = re.search(
                SDD_KEY_START_RIGHT_REGEX, line).start()
            key_end_location = re.search(SDD_KEY_END_RIGHT_REGEX, line).start()
            new_line = re.sub(SDD_REPLACE_RIGHT_REGEX, _get_string_from_atom(
                mapping[line[key_start_location:key_end_location]])+"\",", new_line)
        result += new_line+"""
"""
    return result