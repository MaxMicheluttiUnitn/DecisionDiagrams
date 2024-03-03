"""theory BDD module"""
import time
import re
import os
from typing import List
from pysmt.fnode import FNode
import pydot
from dd import cudd as cudd_bdd
from string_generator import SequentialStringGenerator
from formula import get_atoms
from bdd_walker import BDDWalker
from utils import get_string_from_atom as _get_string_from_atom


def compute_bdd_cudd(phi: FNode,
                     output_file: str = None,
                     dump_abstraction: bool = False,
                     print_mapping: bool = False,
                     count_models: bool = False,
                     count_nodes: bool = False,
                     qvars: List[FNode] = [],
                     computation_logger: any = {}):
    '''Computes the BDD for the boolean formula phi and saves it on a file using dd.cudd'''
    # setting default values
    # if output_file is None:
    #     output_file = "output/bdd.svg"

    # CREATING VARIABLE MAPPING
    start_time = time.time()
    print("Creating mapping...")
    mapping = {}
    atoms = get_atoms(phi)
    string_generator = SequentialStringGenerator()
    for atom in atoms:
        mapping[atom] = string_generator.next_string()
    elapsed_time = (time.time() - start_time)
    print("Mapping created in ", elapsed_time, " seconds")
    computation_logger["BDD"]["variable mapping creation time"] = elapsed_time

    # BUILDING ACTUAL BDD
    start_time = time.time()
    print("Building BDD...")
    bdd = cudd_bdd.BDD()
    appended_values = set()
    mapped_qvars = [mapping[atom] for atom in qvars]
    all_values = [mapping[atom] for atom in qvars]
    for atom in qvars:
        appended_values.add(mapping[atom])
    for value in mapping.values():
        if not value in appended_values:
            all_values.append(value)
    bdd.declare(*all_values)
    bdd_ordering = {}
    for i, item in enumerate(all_values):
        bdd_ordering[item] = i
    cudd_bdd.reorder(bdd, bdd_ordering)
    walker = BDDWalker(mapping, bdd)
    root = walker.walk(phi)
    elapsed_time = (time.time() - start_time)
    print("BDD for phi built in ", elapsed_time, " seconds")
    computation_logger["BDD"]["DD building time"] = elapsed_time

    # ENUMERATING OVER FRESH T-ATOMS
    if len(mapped_qvars) > 0:
        start_time = time.time()
        print("Enumerating over fresh T-atoms...")
        root = cudd_bdd.and_exists(root, bdd.true, mapped_qvars)
        elapsed_time = (time.time() - start_time)
        print("BDD for phi built in ", elapsed_time, " seconds")
        computation_logger["BDD"]["fresh T-atoms quantification time"] = elapsed_time
    else:
        computation_logger["BDD"]["fresh T-atoms quantification time"] = 0

    # COUNTING NODES
    if count_nodes:
        total_nodes = len(root)
        print("Nodes in BDD: ", total_nodes)
        computation_logger["BDD"]["DD nodes"] = total_nodes

    # MODEL COUNTING
    if count_models:
        start_time = time.time()
        print("Counting models...")
        total_models = root.count(nvars=len(mapping.keys())-len(qvars))
        print("Models: ", total_models)
        computation_logger["BDD"]["model count"] = total_nodes
        elapsed_time = (time.time() - start_time)
        print("Models counted in ", elapsed_time, " seconds")
        computation_logger["BDD"]["model counting time"] = elapsed_time

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
            return
        elapsed_time = time.time()-start_time
        print("BDD saved as "+output_file+" in ",
              elapsed_time, " seconds")
        computation_logger["BDD"]["dumping time"] = elapsed_time


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
