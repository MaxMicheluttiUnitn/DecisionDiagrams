import time
import re
import pydot

from pysmt.fnode import FNode
from pysdd.sdd import SddManager, Vtree
from dd.autoref import BDD, Function
from dd import cudd as cudd_bdd
from string_generator import SequentailStringGenerator
from formula import get_atoms, get_phi
from sdd_walker import SDDWalker
from bdd_walker import BDDWalker
from bdd_cudd_walker import BDDCUDDParser


def compute_sdd(phi: FNode, vtree_type: str = None, output_file: str = None, vtree_output: str = None) -> None:
    ' ' 'Computes the SDD for the boolean formula phi and saves it on a file' ' '
    # Setting default values
    if vtree_type is None:
        vtree_type = "right"
    if output_file is None:
        output_file = "sdd.dot"

    # BUILDING V-TREE
    start_time = time.time()
    print("Building V-Tree...")
    atoms = get_atoms(phi)
    var_count = len(atoms)
    # for now just use appearance order in phi
    var_order = list(range(1, var_count + 1))
    vtree = Vtree(var_count, var_order, vtree_type)
    print("V-Tree built in ", time.time()-start_time, " seconds")

    # SAVING VTREE
    if not vtree_output is None:
        start_time = time.time()
        print("Saving V-Tree...")
        if _save_SDD_object(vtree, vtree_output):
            print("V-Tree saved as "+vtree_output+" in ",
                  time.time()-start_time, " seconds")
        else:
            print("V-Tree could not be saved: The file format of ",
                  vtree_output, " is not supported")

    # BUILDING SDD WITH WALKER
    start_time = time.time()
    print("Building SDD...")
    manager = SddManager.from_vtree(vtree)
    sdd_literals = [manager.literal(i) for i in range(1, var_count + 1)]
    atom_literal_map = dict(zip(atoms, sdd_literals))
    print(atom_literal_map)
    walker = SDDWalker(atom_literal_map, manager)
    sdd_formula = walker.walk(phi)
    print("SDD build in ", time.time()-start_time, " seconds")

    # SAVING SDD
    start_time = time.time()
    print("Saving SDD...")
    if _save_SDD_object(sdd_formula, output_file):
        print("SDD saved as "+output_file+" in ",
              time.time()-start_time, " seconds")
    else:
        print("SDD could not be saved: The file format of ",
              output_file, " is not supported")


def _save_SDD_object(sdd_object, output_file: str) -> bool:
    '''saves an SDD object on a file'''
    dot_content = sdd_object.dot()
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


def compute_sdd_formula(phi: FNode, mapping: dict[FNode, int]) -> int:
    '''computes the SDD formula from phi'''
    return compute_sdd_formula_recursive(phi, mapping)


def compute_sdd_formula_recursive(source: FNode, mapping: dict[FNode, int]) -> int:
    '''computes the SDD formula from phi recursively'''
    if source.is_not():
        result = ~ compute_sdd_formula_recursive(source.args()[0], mapping)
        return result
    if not source.is_bool_op():
        return mapping[source]
    subformulae = source.args()
    translated_subformulae = list(
        map(lambda x: compute_sdd_formula_recursive(x, mapping), subformulae))
    if len(translated_subformulae) <= 0:
        raise Exception("Boolean operator without children found")
    if source.is_and():
        if len(translated_subformulae) == 1:
            return translated_subformulae[0]
        result = translated_subformulae[0] & translated_subformulae[1]
        for i in range(2, len(translated_subformulae)):
            result = result & translated_subformulae[i]
        return result
    if source.is_or():
        if len(translated_subformulae) == 1:
            return translated_subformulae[0]
        result = translated_subformulae[0] | translated_subformulae[1]
        for i in range(2, len(translated_subformulae)):
            result = result | translated_subformulae[i]
        return result
    if source.is_iff():
        if len(translated_subformulae) == 1:
            return translated_subformulae[0]
        return (translated_subformulae[0] & translated_subformulae[1]) | ((~ translated_subformulae[0]) & (~ translated_subformulae[1]))


def compute_bdd(phi: FNode, output_file=None) -> None:
    '''Computes the BDD for the boolean formula phi and saves it on a file using dd.autoref'''
    # For now always use compute_bdd_cudd
    return compute_bdd_cudd(phi, output_file)
    if output_file is None:
        output_file = "bdd.svg"
    bdd = BDD()
    atoms = get_atoms(phi)
    mapping = {}
    string_generator = SequentailStringGenerator()
    for atom in atoms:
        mapping[atom] = string_generator.next_string()
    all_values = []
    for value in mapping.values():
        all_values.append(value)
    bdd.declare(*all_values)
    walker = BDDWalker(mapping, bdd)
    root = walker.walk(phi)
    bdd.collect_garbage()
    bdd.dump("bdd.svg", filetype='svg', roots=[root])
    # bdd.dump(output_file, filetype='svg')


def compute_bdd_cudd(phi: FNode, output_file=None):
    '''Computes the BDD for the boolean formula phi and saves it on a file using dd.cudd'''
    # setting default values
    if output_file is None:
        output_file = "bdd.svg"

    # REPRESENT PHI IN PROMELA SYNTAX
    start_time = time.time()
    print("Translating phi...")
    mapping = {}
    atoms = get_atoms(phi)
    string_generator = SequentailStringGenerator()
    for atom in atoms:
        mapping[atom] = string_generator.next_string()
    walker = BDDCUDDParser(mapping)
    translated_phi = walker.walk(phi)
    print("Phi translated in ", (time.time() - start_time), " seconds")

    # BUILDING ACTUAL BDD
    start_time = time.time()
    print("Building BDD...")
    bdd = cudd_bdd.BDD()
    all_values = []
    for value in mapping.values():
        all_values.append(value)
    bdd.declare(*all_values)
    root = bdd.add_expr(translated_phi)
    print("BDD for phi built in ", (time.time() - start_time), " seconds")

    # SAVING BDD
    start_time = time.time()
    print("Saving BDD...")
    bdd.dump(output_file, filetype='svg', roots=[root])
    # translate svg variables in original variables
    reverse_mapping = dict((v, k) for k, v in mapping.items())
    _change_svg_names(output_file, reverse_mapping)
    print("BDD saved as "+output_file+" in ",
          time.time()-start_time, " seconds")


LINE_REGEX = r">[a-z]+&#45;[0-9]+</text>"
KEY_START_REGEX = r"[a-z]+&#45;[0-9]+<"
KEY_END_REGEX = r"&#45;[0-9]+<"
REPLECE_REGEX = r">[a-z]+&#45;[0-9]+<"


def _change_svg_names(output_file, mapping):
    '''Changes the names into the svg to match theory atoms' names'''
    svg_file = open(output_file, 'r')
    svg_lines = svg_file.readlines()
    svg_output = """"""
    for line in svg_lines:
        found = re.search(LINE_REGEX, line)
        if not found is None:
            key_start_location = re.search(KEY_START_REGEX, line).start()
            key_end_location = re.search(KEY_END_REGEX, line).start()
            line = re.sub(REPLECE_REGEX, _get_string_from_atom(
                mapping[line[key_start_location:key_end_location]]), line)
        svg_output += line
    svg_file.close()
    with open(output_file, 'w') as out:
        print(svg_output, file=out)


def _get_string_from_atom(atom):
    '''Changes special characters into ASCII encoding'''
    # svg format special characters source: https://rdrr.io/cran/RSVGTipsDevice/man/encodeSVGSpecialChars.html
    atom_str = str(atom).replace('&', '&#38;').replace('\'', "&#30;").replace(
        '"', "&#34;").replace('<', '&#60;').replace('>', "&#62;")
    return ">"+atom_str[1:len(atom_str)-1]+"<"


def compute_bdd_formula(phi: FNode, mapping: dict[FNode, str], handler: BDD):
    '''Computes the BDD formula'''
    return compute_bdd_formula_recursive(phi, mapping, handler)


def compute_bdd_formula_recursive(source: FNode, mapping: dict[FNode, str], handler: BDD) -> Function:
    '''Computes the BDD formula recursively'''
    if source.is_not():
        result = ~ compute_bdd_formula_recursive(
            source.args()[0], mapping, handler)
        return result
    if not source.is_bool_op():
        return handler.add_expr(mapping[source])
    subformulae = source.args()
    translated_subformulae = list(
        map(lambda x: compute_bdd_formula_recursive(x, mapping, handler), subformulae))
    if len(translated_subformulae) <= 0:
        raise Exception("Boolean operator without children found")
    if source.is_and():
        if len(translated_subformulae) == 1:
            return translated_subformulae[0]
        result = translated_subformulae[0] & translated_subformulae[1]
        for i in range(2, len(translated_subformulae)):
            result = result & translated_subformulae[i]
        return result
    if source.is_or():
        if len(translated_subformulae) == 1:
            return translated_subformulae[0]
        result = translated_subformulae[0] | translated_subformulae[1]
        for i in range(2, len(translated_subformulae)):
            result = result | translated_subformulae[i]
        return result
    if source.is_iff():
        if len(translated_subformulae) == 1:
            return translated_subformulae[0]
        result = (translated_subformulae[0] & translated_subformulae[1]) | (
            (~ translated_subformulae[0]) & (~ translated_subformulae[1]))
        return result


if __name__ == "__main__":
    test_phi = get_phi()
    # compute_bdd(test_phi)
    # compute_sdd(test_phi)
