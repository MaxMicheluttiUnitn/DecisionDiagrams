'''this module builds an handles DDs from pysmt formulas'''

import time
import re
import os
import pydot

from array import array
from typing import List
from pysmt.fnode import FNode
from pysmt.shortcuts import BOOL, REAL, Real, Times, INT
from pysdd.sdd import SddManager, Vtree, WmcManager
from dd.autoref import BDD, Function
from dd import cudd as cudd_bdd
from pywmi.domain import Domain
from pywmi import XsddEngine
from pywmi.engines.xsdd.engine import extract_and_replace_literals
from pywmi.engines.xsdd.smt_to_sdd import compile_to_sdd

from string_generator import SequentailStringGenerator, SDDSequentailStringGenerator
from formula import get_atoms, get_phi, get_symbols
from sdd_walker import SDDWalker
from bdd_walker import BDDWalker
# from bdd_cudd_walker import BDDCUDDParser
from xsdd_walker import XsddParser


def compute_xsdd(phi: FNode):
    '''computing xsdd'''
    symbols = get_symbols(phi)

    boolean_symbols = []
    real_symbols = []
    # real_bounds=[]

    for symbol in symbols:
        if symbol.get_type() == BOOL:
            boolean_symbols.append("xsdd_"+str(symbol))
        elif symbol.get_type() == REAL:
            real_symbols.append("xsdd_"+str(symbol))
        elif symbol.get_type() == INT:
            real_symbols.append("xsdd_"+str(symbol))
            # just putting very big bounds to let not limit the variable
            # real_bounds.append((-1000000,1000000))

    # bounds are necesssary (XSDD are designed for WMI), so I just put them very big
    xsdd_domain = Domain.make(
        boolean_symbols, real_symbols, real_bounds=(-1000000, 1000000))

    xsdd_boolean_symbols = xsdd_domain.get_bool_symbols()
    xsdd_real_symbols = xsdd_domain.get_real_symbols()
    weight_function = Times(
        Real(2), xsdd_real_symbols[0], xsdd_real_symbols[1])

    walker = XsddParser(boolean_symbols, xsdd_boolean_symbols,
                        real_symbols, xsdd_real_symbols)
    xsdd_support: FNode = walker.walk(phi)

    xsdd_engine = XsddEngine(xsdd_domain, xsdd_support, weight_function)

    # _, xsdd_support, literals = extract_and_replace_literals(xsdd_support)
    # xsdd_sdd = xsdd_engine.get_sdd(
    #     xsdd_support, literals, xsdd_engine.get_vtree(xsdd_support, literals))
    # print(xsdd_sdd)

    # xsdd_other_sdd = compile_to_sdd(xsdd_support, literals, None)

    # with open('sdd_00.dot', 'w') as out:
    #     out.write(xsdd_sdd.dot())

    # with open('sdd_other_00.dot', 'w') as out:
    #     out.write(xsdd_other_sdd.dot())

    print(xsdd_engine.compute_volume(add_bounds=False))


def compute_sdd(phi: FNode,
                vtree_type: str = None,
                output_file: str = None,
                vtree_output: str = None,
                dump_abstraction: bool = False,
                print_mapping: bool = False,
                count_models: bool = False,
                qvars: List[FNode] = [],
                all_sat_models: List = None) -> None:
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
    print("V-Tree built in ", time.time()-start_time, " seconds")

    # SAVING VTREE
    if not vtree_output is None:
        start_time = time.time()
        print("Saving V-Tree...")
        if _save_sdd_object(vtree, vtree_output, name_to_atom_map, 'VTree'):
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
    walker = SDDWalker(atom_literal_map, manager)
    sdd_formula = walker.walk(phi)
    existential_map = [0]
    for smt_atom in atom_literal_map.keys():
        if smt_atom in qvars:
            existential_map.append(1)
        else:
            existential_map.append(0)
    sdd_formula = manager.exists_multiple(array('i',existential_map),sdd_formula)
    # for num in existential_map:
    #     sdd_formula = manager.exists(num,sdd_formula)
    print("SDD built in ", time.time()-start_time, " seconds")

    # EQUIVALENCE CHECKING
    # if not all_sat_models is None:
    #     c=0
    #     for model in all_sat_models:
    #         conditioned = sdd_formula
    #         for atom in model:
    #             if atom.is_not():
    #                 lit = atom_literal_map[atom.args()[0]]
    #                 conditioned = conditioned & -lit
    #             else:
    #                 lit = atom_literal_map[atom]
    #                 conditioned = conditioned & lit
    #         wmc: WmcManager = conditioned.wmc(log_mode=False)
    #         w = wmc.propagate()
    #         c+=1
    #         print(f"{c} : Model count: {w}")
    
    # MODEL COUNTING
    if count_models:
        start_time = time.time()
        print("Counting models through the SDD...")
        wmc: WmcManager = sdd_formula.wmc(log_mode=False)
        w = wmc.propagate()/(2**len(qvars))
        print(f"Model count: {w}")
        print("Models counted in ", time.time()-start_time, " seconds")

    # SAVING SDD
    if not output_file is None:
        start_time = time.time()
        print("Saving SDD...")
        if print_mapping:
            print("Mapping:")
            print(name_to_atom_map)
        if _save_sdd_object(sdd_formula, output_file, name_to_atom_map, 'SDD', dump_abstraction):
            print("SDD saved as "+output_file+" in ",
                time.time()-start_time, " seconds")
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
        return (translated_subformulae[0] & translated_subformulae[1]) | (
            (~ translated_subformulae[0]) & (~ translated_subformulae[1]))


def compute_bdd(phi: FNode, output_file=None, dump_abstraction=False, print_mapping=False) -> None:
    '''Computes the BDD for the boolean formula phi and saves it on a file using dd.autoref'''
    # For now always use compute_bdd_cudd
    return compute_bdd_cudd(phi, output_file, dump_abstraction, print_mapping)
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


def compute_bdd_cudd(phi: FNode,
                     output_file: str = None,
                     dump_abstraction: bool = False,
                     print_mapping: bool = False,
                     count_models: bool = False,
                     qvars: List[FNode] = [],
                     all_sat_models: List = None):
    '''Computes the BDD for the boolean formula phi and saves it on a file using dd.cudd'''
    # setting default values
    # if output_file is None:
    #     output_file = "output/bdd.svg"

    # REPRESENT PHI IN PROMELA SYNTAX
    start_time = time.time()
    print("Creating mapping...")
    mapping = {}
    atoms = get_atoms(phi)
    string_generator = SequentailStringGenerator()
    for atom in atoms:
        mapping[atom] = string_generator.next_string()
    print("Mapping created in ", (time.time() - start_time), " seconds")

    # BUILDING ACTUAL BDD
    start_time = time.time()
    print("Building BDD...")
    bdd = cudd_bdd.BDD()
    all_values = []
    for value in mapping.values():
        all_values.append(value)
    mapped_qvars = []
    for atom in qvars:
        mapped_qvars.append(mapping[atom])
    bdd.declare(*all_values)
    walker = BDDWalker(mapping, bdd)
    root = walker.walk(phi)
    all_values = []
    if len(mapped_qvars) > 0:
        root = cudd_bdd.and_exists(root, bdd.true, mapped_qvars)
    # root = bdd.add_expr(translated_phi)
    print("BDD for phi built in ", (time.time() - start_time), " seconds")

    # MODEL COUNTING
    if count_models:
        start_time = time.time()
        print("Counting models...")
        print("Models:")
        print(root.count(nvars=len(mapping.keys())-len(qvars)))
        print("Models counted in ", (time.time() - start_time), " seconds")

    # SAVING BDD
    if not output_file is None:
        start_time = time.time()
        print("Saving BDD...")
        temporary_dot = 'bdd_temporary_dot.dot'
        reverse_mapping = dict((v, k) for k, v in mapping.items())
        if print_mapping:
            print("Mapping:")
            print(reverse_mapping)
        if output_file.endswith('.dot'):
            bdd.dump(output_file, filetype='dot', roots=[root])
            if not dump_abstraction:
                _change_bbd_dot_names(output_file, reverse_mapping)
        elif output_file.endswith('.svg'):
            bdd.dump(temporary_dot, filetype='dot', roots=[root])
            if not dump_abstraction:
                _change_bbd_dot_names(temporary_dot, reverse_mapping)
            with open(temporary_dot, 'r') as dot_content:
                (graph,) = pydot.graph_from_dot_data(dot_content.read())
                graph.write_svg(output_file)
            os.remove(temporary_dot)
        else:
            print('Unable to dump BDD file: format unsupported')
        print("BDD saved as "+output_file+" in ",
          time.time()-start_time, " seconds")


BDD_DOT_LINE_REGEX = r'[\[]label="[a-z]*-[0-9]*"[]]'
BDD_DOT_TRUE_LABEL = '[label="True-1"]'
BDD_DOT_KEY_START_REGEX = r'"[a-z]*-[0-9]*"]'
BDD_DOT_KEY_END_REGEX = r'-[0-9]*"]'
BDD_DOT_REPLACE_REGEX = BDD_DOT_LINE_REGEX


def _change_bbd_dot_names(output_file, mapping):
    '''changes the name in the dot file with the actual names of the atoms'''
    dot_file = open(output_file, 'r')
    dot_lines = dot_file.readlines()
    dot_output = """"""
    for line in dot_lines:
        found = re.search(BDD_DOT_LINE_REGEX, line)
        if not found is None:
            key_start_location = re.search(
                BDD_DOT_KEY_START_REGEX, line).start() + 1
            key_end_location = re.search(BDD_DOT_KEY_END_REGEX, line).start()
            line = re.sub(BDD_DOT_REPLACE_REGEX, "[label=\""+_get_string_from_atom(
                mapping[line[key_start_location:key_end_location]])+"\"]", line)
        dot_output += line
    dot_file.close()
    with open(output_file, 'w') as out:
        print(dot_output, file=out)


BDD_LINE_REGEX = r">[a-z]+&#45;[0-9]+</text>"
BDD_KEY_START_REGEX = r"[a-z]+&#45;[0-9]+<"
BDD_KEY_END_REGEX = r"&#45;[0-9]+<"
BDD_REPLECE_REGEX = r">[a-z]+&#45;[0-9]+<"


def _change_svg_names(output_file, mapping):
    '''Changes the names into the svg to match theory atoms' names'''
    svg_file = open(output_file, 'r')
    svg_lines = svg_file.readlines()
    svg_output = """"""
    for line in svg_lines:
        found = re.search(BDD_LINE_REGEX, line)
        if not found is None:
            key_start_location = re.search(BDD_KEY_START_REGEX, line).start()
            key_end_location = re.search(BDD_KEY_END_REGEX, line).start()
            line = re.sub(BDD_REPLECE_REGEX, ">"+_get_string_from_atom(
                mapping[line[key_start_location:key_end_location]])+"<", line)
        svg_output += line
    svg_file.close()
    with open(output_file, 'w') as out:
        print(svg_output, file=out)


def _get_string_from_atom(atom):
    '''Changes special characters into ASCII encoding'''
    # svg format special characters source:
    # https://rdrr.io/cran/RSVGTipsDevice/man/encodeSVGSpecialChars.html
    atom_str = str(atom).replace('&', '&#38;').replace('\'', "&#30;").replace(
        '"', "&#34;").replace('<', '&#60;').replace('>', "&#62;")
    if atom_str.startswith('('):
        return atom_str[1:len(atom_str)-1]
    return atom_str


def compute_bdd_formula(phi: FNode, mapping: dict[FNode, str], handler: BDD):
    '''Computes the BDD formula'''
    return compute_bdd_formula_recursive(phi, mapping, handler)


def compute_bdd_formula_recursive(source: FNode,
                                  mapping: dict[FNode, str], handler: BDD) -> Function:
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
