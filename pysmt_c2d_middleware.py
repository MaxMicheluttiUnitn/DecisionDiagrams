"""midddleware for pysmt-c2d compatibility"""

import random
import os
import time
from typing import Dict, List, Tuple
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
from theorydd.formula import save_mapping, load_mapping

# load c2d executable location from dotenv
from dotenv import load_dotenv as _load_env
_load_env()
_C2D_EXECUTABLE = os.getenv("C2D_BINARY")

# fix command to launch c2d compiler
if _C2D_EXECUTABLE is not None and os.path.isfile(_C2D_EXECUTABLE) and not _C2D_EXECUTABLE.startswith("."):
    if _C2D_EXECUTABLE.startswith("/"):
        _C2D_EXECUTABLE = f".{_C2D_EXECUTABLE}"
    else:
        _C2D_EXECUTABLE = f"./{_C2D_EXECUTABLE}"


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

    # check if formula is top
    if phi_cnf.is_true():
        with open(dimacs_file, "w", encoding="utf8") as dimacs_out:
            dimacs_out.write("p cnf 1 1\n1 -1 0\n")
        return mapping

    # check if formula is bottom
    if phi_cnf.is_false():
        with open(dimacs_file, "w", encoding="utf8") as dimacs_out:
            dimacs_out.write("p cnf 1 2\n1 0\n-1 0\n")
        return mapping

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


def count_nodes_and_edges_from_c2d_nnf(c2d_file: str) -> Tuple[int, int]:
    """
    Counts nodes and edges of the formula contained in the file c2d_file from nnf format to a pysmt FNode

    Args:
        c2d_file (str) -> the path to the file where the dimacs output needs to be saved

    Returns:
        (int,int) -> the total nodes and edges of the formula (#nodes,#edges)
    """
    total_nodes = 0
    total_edges = 0
    with open(c2d_file, "r", encoding="utf8") as data:
        contents = data.read()
    lines: List[str] = contents.split("\n")
    lines = list(filter(lambda x: x != "", lines))
    for line in lines:
        if line.startswith("nnf "):
            # I DO NOT CARE ABOUT THIS DATA FOR PARSING
            continue
        elif line.startswith("A "):
            # AND node
            total_nodes += 1
            if line.startswith("A 0"):
                continue
            tokens = line.split(" ")[2:]
            and_nodes = [int(t) for t in tokens]
            if len(and_nodes) == 1:
                total_edges += 1
                continue
            total_edges += len(and_nodes)
        elif line.startswith("O "):
            # OR node
            total_nodes += 1
            tokens = line.split(" ")[1:]
            _j = tokens[0]
            tokens = tokens[1:]
            c = tokens[0]
            tokens = tokens[1:]
            if c == "0":
                continue
            or_nodes = [int(t) for t in tokens]
            if len(or_nodes) == 1:
                total_edges += 1
                continue
            total_edges += len(or_nodes)
        elif line.startswith("L "):
            # LITERAL
            # tokens = line.split(" ")[1:]
            # variable = int(tokens[0])
            total_nodes += 1
            # if variable > 0:
            # pysmt_nodes.append(mapping[variable])
            # total_nodes += 1
            # else:
            # total_nodes += 1
            # pysmt_nodes.append(Not(mapping[abs(variable)]))
    return (total_nodes, total_edges)


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


def compile_dDNNF(
        phi: FNode,
        keep_temp: bool = False,
        tmp_path: str | None = None,
        computation_logger: Dict | None = None,
        verbose: bool = False,
        back_to_fnode: bool = True) -> Tuple[FNode | None, int, int]:
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
        Tuple[FNode,int,int] | None -> if back_to_fnode is set to True, the function returns:
        (FNode) -> the input pysmt formula in dDNNF
        (int) -> the number of nodes in the dDNNF
        (int) -> the number of edges in the dDNNF
    """
    # check if c2d is available and executable
    if _C2D_EXECUTABLE is None or not os.path.isfile(_C2D_EXECUTABLE):
        raise FileNotFoundError(
            "The binary for the c2d compiler is missing. Please check the installation path and update the .env file.")
    if not os.access(_C2D_EXECUTABLE, os.X_OK):
        raise PermissionError(
            "The c2d binary is not executable. Please check the permissions for the file and grant execution rights.")

    # failsafe for computation_logger
    if computation_logger is None:
        computation_logger = {}

    computation_logger["dDNNF compiler"] = "c2d"

    # choose temporary folder
    if tmp_path is None:
        tmp_folder = "temp_" + str(random.randint(0, 9223372036854775807))
    else:
        tmp_folder = tmp_path

    # translate to CNF DIMACS and get mapping used for translation
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
    # compute reverse mapping to translate back to pysmt (REFINEMENT)
    reverse_mapping = {v: k for k, v in mapping.items()}

    # save mapping for refinement
    if not os.path.exists(f"{tmp_folder}/mapping"):
        os.mkdir(f"{tmp_folder}/mapping")
    if verbose:
        print("Saving mapping...")
    save_mapping(reverse_mapping, f"{tmp_folder}/mapping")
    if verbose:
        print("Mapping saved")

    # call c2d for compilation
    # output should be in file temp_folder/test_dimacs.cnf.nnf
    start_time = time.time()
    if verbose:
        print("Compiling dDNNF...")
    result = os.system(
        f"timeout 3600s {_C2D_EXECUTABLE} -in {tmp_folder}/dimacs.cnf -exist {tmp_folder}/quantification.exist > /dev/null"
    )
    if result != 0:
        raise TimeoutError("c2d compilation failed: timeout")
    elapsed_time = time.time() - start_time
    computation_logger["dDNNF compilation time"] = elapsed_time
    if verbose:
        print(f"dDNNF compilation completed in {elapsed_time} seconds")

    # counting size
    nodes, edges = count_nodes_and_edges_from_c2d_nnf(
        f"{tmp_folder}/dimacs.cnf.nnf")

    # return if not back to fnode
    if not back_to_fnode:
        return None, nodes, edges

    # loading saved mapping
    # reverse_mapping = load_mapping(f"{tmp_folder}/mapping/mapping.json")

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
    return result, nodes, edges


def load_dDNNF(nnf_path: str, mapping_path: str) -> FNode:
    """
    Load a dDNNF from file and translate it to pysmt

    Args:
        nnf_path (str) ->       the path to the file containing the dDNNF in 
                                NNF format provided by the c2d compiler
        mapping_path (str) ->   the path to the file containing the mapping

    Returns:
        (FNode) -> the pysmt formula translated from the dDNNF
    """
    mapping = load_mapping(mapping_path)
    return from_c2d_nnf_to_pysmt(nnf_path, mapping)


if __name__ == "__main__":
    test_phi = read_smtlib("test.smt2")

    print(test_phi.serialize())

    phi_ddnnf, _a, _b = compile_dDNNF(test_phi, back_to_fnode=True)

    print(phi_ddnnf.serialize())
