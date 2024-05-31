"""midddleware for pysmt-c2d compatibility"""

import random
import os
import time
from typing import Dict, List
from pysmt.shortcuts import (
    write_smtlib,
    read_smtlib,
    And,
    Or,
    get_atoms,
    TRUE,
    FALSE,
    Not,
)
from pysmt.fnode import FNode

from allsat_cnf.label_cnfizer import LabelCNFizer


def from_smtlib_to_dimacs_file(
    smt_data: str | FNode,
    dimacs_file: str,
    quantification_file: str,
    mapping: Dict[FNode, int] | None = None,
) -> Dict[FNode, int]:
    """
    translates an SMT formula in DIMACS format and saves it on file.
    All fresh variables are saved inside quantification_file.
    The mapping use to translate the formula is then returned.

    Args:
        smt_data (str | FNode) -> if a str is passed, data is read from the corresponding file,
            if a FNode is passed, the fomula translated is the one described by the FNode
        dimacs_file (str) -> the path to the file where the dimacs output need to be saved
        quantification_file (str) -> the path to the file where the quantified variables
            need to be saved
        mapping (Dict[FNode, int] | None) = None -> a mapping that associates a positive
            integer to each atom in the formula

    Returns:
        (Dict[FNode, int]) -> the mapping used to translate the formula
    """
    if isinstance(smt_data, str):
        phi: FNode = read_smtlib(smt_data)
    else:
        phi = smt_data
    phi_cnf: FNode = LabelCNFizer().convert_as_formula(phi)
    phi_atoms: frozenset = get_atoms(phi)
    phi_cnf_atoms: frozenset = get_atoms(phi_cnf)
    fresh_atoms: List[FNode] = list(phi_cnf_atoms.difference(phi_atoms))
    if mapping is None:
        # create new mapping
        count = 1
        mapping = {}
    else:
        # extend old mapping
        count = len(phi_atoms) + 1
    for atom in phi_cnf_atoms:
        mapping[atom] = count
        count += 1

    # CONVERTNG IN DIMACS FORMAT AND SAVING ON FILE
    total_variables = len(mapping.keys())
    clauses: List[FNode] = phi_cnf.args()
    total_clauses = len(clauses)
    with open(dimacs_file, "w", encoding="utf8") as dimacs_out:
        dimacs_out.write(f"p cnf {total_variables} {total_clauses}\n")
        for clause in clauses:
            if clause.is_or():
                literals: List[FNode] = clause.args()
                translated_literals: List[int] = []
                for literal in literals:
                    if literal.is_not():
                        negated_literal: FNode = literal.arg(0)
                        translated_literals.append(
                            str(mapping[negated_literal] * -1))
                    else:
                        translated_literals.append(str(mapping[literal]))
                line = " ".join(translated_literals)
            elif clause.is_not():
                negated_literal: FNode = clause.arg(0)
                line = str(mapping[negated_literal] * -1)
            else:
                line = str(mapping[clause])
            dimacs_out.write(line)
            dimacs_out.write(" 0\n")

    # SAVING QUANTIFICATION FILE
    with open(quantification_file, "w", encoding="utf8") as quantification_out:
        quantified_indexes = [str(mapping[atom]) for atom in fresh_atoms]
        quantified_indexes_str: str = " ".join(quantified_indexes)
        quantification_out.write(
            f"{len(quantified_indexes)} {quantified_indexes_str}")

    # RETURN MAPPING
    return mapping


def from_c2d_nnf_to_pysmt(c2d_file: str, mapping: Dict[int, FNode]) -> FNode:
    """
    Translates the formula contained in the file c2d_file from nnf format to a pysmt FNode

    Args:
        c2d_file (str) -> the path to the file where the dimacs output need to be saved
        mapping (Dict[int,FNode]) -> a mapping that associates to integers a pysmt atom,
            used to translate the variables from their abstraction in the nnf format to pysmt

    Returns:
        (FNode) -> the pysmt formula read from the file
    """
    with open(c2d_file, "r", encoding="utf8") as data:
        contents = data.read()
    lines: List[str] = contents.split("\n")
    lines = list(filter(lambda x: x != "", lines))
    pysmt_nodes: List[FNode] = []
    for line in lines:
        if line.startswith("nnf "):
            # I DO NOT CARE ABOUT THIS DATA FOR PARSING
            continue
        elif line.startswith("A "):
            # AND node
            if line.startswith("A 0"):
                pysmt_nodes.append(TRUE())
                continue
            tokens = line.split(" ")[2:]
            and_nodes = [pysmt_nodes[int(t)] for t in tokens]
            if len(and_nodes) == 1:
                pysmt_nodes.append(and_nodes[0])
                continue
            pysmt_nodes.append(And(*and_nodes))
        elif line.startswith("O "):
            # OR node
            tokens = line.split(" ")[1:]
            _j = tokens[0]
            tokens = tokens[1:]
            c = tokens[0]
            tokens = tokens[1:]
            if c == "0":
                pysmt_nodes.append(FALSE())
                continue
            or_nodes = [pysmt_nodes[int(t)] for t in tokens]
            if len(or_nodes) == 1:
                pysmt_nodes.append(or_nodes[0])
                continue
            pysmt_nodes.append(Or(*or_nodes))
        elif line.startswith("L "):
            # LITERAL
            tokens = line.split(" ")[1:]
            variable = int(tokens[0])
            if variable > 0:
                pysmt_nodes.append(mapping[variable])
            else:
                pysmt_nodes.append(Not(mapping[abs(variable)]))
    return pysmt_nodes[len(pysmt_nodes) - 1]


def from_c2d_nnf_to_smtlib(
    c2d_file: str, smtlib_file: str, mapping: Dict[int, FNode]
) -> None:
    """
    Translates the formula inside c2d_file from nnf format to pysmt
    FNode and saves it in a SMT-Lib file.

    Args:
        c2d_file (str) -> the path to the file where the dimacs output need to be saved
        smtlib_file (str) -> the path to a file that will be overwritten with the
            output SMT-Lib formula
        mapping (Dict[int,FNode]) -> a mapping that associates to integers a pysmt atom,
            used to translate the variables from their abstraction in the nnf format to pysmt
    """
    phi = from_c2d_nnf_to_pysmt(c2d_file, mapping)
    write_smtlib(phi, smtlib_file)


def save_mapping(mapping: Dict[int, FNode], mapping_path: str) -> None:
    """
    Saves a mapping from integers to pysmt atoms in a file

    Args:
        mapping (Dict[int,FNode]) -> a mapping that associates to integers a pysmt atom
        mapping_path (str) -> the path to the folder where the mapping files will be saved
    """
    for k, v in mapping.items():
        write_smtlib(v, f"{mapping_path}/{k}.smt2")
        # with open(f"{mapping_path}/{k}.smt2", "w", encoding="utf8") as mapping_out:
        #     mapping_out.write(f"{k}\n{v.serialize()}\n")


def load_mapping(mapping_path: str) -> Dict[int, FNode]:
    """
    Loads a mapping from integers to pysmt atoms from a file

    Args:
        mapping_path (str) -> the path to the folder where the mapping is saved

    Returns:
        (Dict[int,FNode]) -> a mapping that associates to integers a pysmt atom
    """
    mapping = {}
    for filename in os.listdir(mapping_path):
        if filename.endswith(".smt2"):
            k = int(filename.split(".")[0])
            v = read_smtlib(f"{mapping_path}/{filename}")
            mapping[k] = v
    return mapping


def compile_dDNNF(phi: FNode, keep_temp: bool = False, tmp_path: str | None = None, computation_logger: Dict | None = None, verbose: bool = False, back_to_fnode: bool = True) -> FNode | None:
    """
    Compiles an FNode in dDNNF through the c2d compiler

    Args:
        phi (FNode) -> a pysmt formula
        keep_temp (bool) = False -> set it to true to keep temporary computation data
        tmp_path (str | None) = None -> the path where temporary data will be saved. 
            If keep_temp is set to False, this path is removed from the system after 
            computation is ccompleted
        computation_logger (Dict | None) = None -> a dictionary that will be filled with
            data about the computation
        verbose (bool) = False -> set it to True to print information about the computation
        back_to_fnode (bool) = True -> set it to False to avoid the final pysmt translation

    Returns:
        (FNode) -> the input pysmt formula in dDNNF
    """
    if computation_logger is None:
        computation_logger = {}
    if tmp_path is None:
        tmp_folder = "temp_" + str(random.randint(0, 9223372036854775807))
    else:
        tmp_folder = tmp_path
    # translate to CNF
    if not os.path.exists(tmp_folder):
        os.mkdir(tmp_folder)
    start_time = time.time()
    if verbose:
        print("Translating to DIMACS...")
    mapping = from_smtlib_to_dimacs_file(
        phi, f"{tmp_folder}/dimacs.cnf", f"{tmp_folder}/quantification.exist"
    )
    elapsed_time = time.time() - start_time
    computation_logger["DIMACS translation time"] = elapsed_time
    if verbose:
        print(f"DIMACS translation completed in {elapsed_time} seconds")
    reverse_mapping = {v: k for k, v in mapping.items()}
    if not os.path.exists(f"{tmp_folder}/mapping"):
        os.mkdir(f"{tmp_folder}/mapping")
    if verbose:
        print("Saving mapping...")
    # TEMPORARILY DISABLED DUE TO DISK MEMORY ISSUES
    #save_mapping(reverse_mapping, f"{tmp_folder}/mapping")
    if verbose:
        print("Mapping saved")
    # call c2d
    # output should be in file temp_folder/test_dimacs.cnf.nnf
    start_time = time.time()
    if verbose:
        print("Compiling dDNNF...")
    result = os.system(
        f"timeout 3600s ./c2d_linux -in {tmp_folder}/dimacs.cnf -exist {tmp_folder}/quantification.exist > /dev/null"
    )
    if result != 0:
        raise TimeoutError("c2d compilation failed: timeout")
    elapsed_time = time.time() - start_time
    computation_logger["dDNNF compilation time"] = elapsed_time
    if verbose:
        print(f"dDNNF compilation completed in {elapsed_time} seconds")
    # reverse_mapping = load_mapping(f"{tmp_folder}/mapping")
    if not back_to_fnode:
        return None
    # translate to pysmt
    start_time = time.time()
    if verbose:
        print("Translating to pysmt...")
    result = from_c2d_nnf_to_pysmt(
        f"{tmp_folder}/dimacs.cnf.nnf", reverse_mapping)
    if os.path.exists(tmp_folder) and not keep_temp:
        os.system(f"rm -rd {tmp_folder}")
    elapsed_time = time.time() - start_time
    computation_logger["pysmt translation time"] = elapsed_time
    if verbose:
        print(f"pysmt translation completed in {elapsed_time} seconds")
    return result


if __name__ == "__main__":
    test_phi = read_smtlib("test.smt2")

    print(test_phi.serialize())

    phi_ddnnf = compile_dDNNF(test_phi, True)

    print(phi_ddnnf.serialize())
