"""midddleware for pysmt-d4 compatibility"""


import random
import os
import time
import re
from typing import Dict, List, Set, Tuple, TypeVar
from dataclasses import dataclass
from dotenv import load_dotenv as _load_env
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
from theorydd.formula import save_mapping, load_mapping, get_phi_and_lemmas

_D4_AND_NODE = 0
_D4_OR_NODE = 1
_D4_TRUE_NODE = 2
_D4_FALSE_NODE = 3

_SelfD4Node = TypeVar("SelfD4Node", bound="D4Node")


@dataclass
class D4Node:
    """a node that results from a d4 compilation process"""
    node_type: int
    edges: Dict[int, List[int]]
    memo: None | FNode

    def __init__(self, node_type: int):
        self.node_type = node_type
        self.edges = {}
        self.memo = None

    def is_ready(self) -> bool:
        """checks if the result for this node has already been computed"""
        return self.memo is not None

    def add_edge(self, dst: int, label: List[int]) -> None:
        """adds an edge to the node"""
        self.edges[dst] = label

    def to_pysmt(self, mapping: Dict[int, FNode], graph: Dict[int, _SelfD4Node]) -> FNode:
        """
        translates the D4Node into a pysmt formula recirsively with memoization

        Args:
            mapping (Dict[int,FNode]) -> a mapping that associates to integers a pysmt atom,
                used to translate the variables from their abstraction in the nnf format to pysmt
            graph (Dict[int,D4Node]) -> the graph containing all the nodes

        Returns:
            (FNode) -> the pysmt formula corresponding to the node
        """
        if self.is_ready():
            return self.memo
        if self.node_type == _D4_TRUE_NODE:
            self.memo = TRUE()
        elif self.node_type == _D4_FALSE_NODE:
            self.memo = FALSE()
        elif self.node_type == _D4_AND_NODE:
            children_pysmts = []
            for dst in self.edges.keys():
                children_pysmts.append(graph[dst].to_pysmt(mapping, graph))
            if len(children_pysmts) == 0:
                raise ValueError("AND node with no children")
            else:
                self.memo = And(*children_pysmts)
        elif self.node_type == _D4_OR_NODE:
            children_pysmts = []
            for dst, label in self.edges.items():
                child_translation = graph[dst].to_pysmt(mapping, graph)
                var_pysmts = []
                for item in label:
                    if item < 0:
                        var_pysmts.append(Not(mapping[abs(item)]))
                    else:
                        var_pysmts.append(mapping[item])
                if len(var_pysmts) == 0:
                    children_pysmts.append(child_translation)
                else:
                    children_pysmts.append(And(*var_pysmts, child_translation))
            if len(children_pysmts) == 0:
                raise ValueError("OR node with no children")
            self.memo = Or(*children_pysmts)
        return self.memo


_RE_NNF_EDGE = re.compile(r"(\d+) (\d+)( .+)? 0")

# load d4 executable location from dotenv
_load_env()
_D4_EXECUTABLE = os.getenv("D4_BINARY")

# fix command to launch d4 compiler
if _D4_EXECUTABLE is not None and os.path.isfile(_D4_EXECUTABLE) and not _D4_EXECUTABLE.startswith("."):
    if _D4_EXECUTABLE.startswith("/"):
        _D4_EXECUTABLE = f".{_D4_EXECUTABLE}"
    else:
        _D4_EXECUTABLE = f"./{_D4_EXECUTABLE}"


def from_smtlib_to_dimacs_file(
    smt_data: str | FNode,
    dimacs_file: str,
    tlemmas: List[FNode] | None = None,
) -> Tuple[Dict[FNode, int], Set[FNode]]:
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
        (Set[Fnode]) -> the set of variables to be forgotten
    """
    if isinstance(smt_data, str):
        phi: FNode = read_smtlib(smt_data)
    else:
        phi = smt_data
    phi_atoms: frozenset = get_atoms(phi)
    if tlemmas is not None:
        phi_and_lemmas = get_phi_and_lemmas(phi, tlemmas)
    else:
        phi_and_lemmas = phi
    phi_cnf: FNode = LabelCNFizer().convert_as_formula(phi_and_lemmas)
    phi_cnf_atoms: frozenset = get_atoms(phi_cnf)
    fresh_atoms: Set[FNode] = frozenset(phi_cnf_atoms.difference(phi_atoms))
    important_atoms_labels: List[int] = []

    # create new mapping
    count = 1
    mapping = {}
    for atom in phi_cnf_atoms:
        if atom in fresh_atoms:
            important_atoms_labels.append(count)
        mapping[atom] = count
        count += 1
        print(atom, ": ", mapping[atom])

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
        # first line
        dimacs_out.write(f"p cnf {total_variables} {total_clauses}\n")
        # second line
        line = "c p show "
        for atom in important_atoms_labels:
            line += f"{atom} "
        line += "0\n"
        dimacs_out.write(line)
        # clause lines
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

    # RETURN MAPPING AND SET OF FRESH ATOMS
    return mapping, fresh_atoms


def from_d4_nnf_to_pysmt(d4_file: str, mapping: Dict[int, FNode]) -> Tuple[FNode, int, int]:
    """
    Translates the formula contained in the file d4_file from nnf format to a pysmt FNode

    Args:
        d4_file (str) -> the path to the file where the dimacs output need to be saved
        mapping (Dict[int,FNode]) -> a mapping that associates to integers a pysmt atom,
            used to translate the variables from their abstraction in the nnf format to pysmt

    Returns:
        (FNode) -> the pysmt formula read from the file
        (int) -> the amount of nodes in the dDNNF
        (int) -> the amount of edges in the dDNNF
    """
    with open(d4_file, "r", encoding="utf8") as data:
        lines: List[str] = data.readlines()
    lines = list(filter(lambda x: x != "", lines))
    total_nodes = 0
    total_arcs = 0
    d4_graph: Dict[int, D4Node] = {}
    for line in lines:
        if line.startswith('o'):
            # OR NODE
            total_nodes += 1
            tokens = line.split(" ")
            if len(tokens) != 3:
                raise ValueError(
                    "Invalid d4 format: OR node with wrong number of tokens")
            node_id = int(tokens[1])
            d4_graph[node_id] = D4Node(_D4_OR_NODE)
        elif line.startswith('a'):
            # AND NODE
            total_nodes += 1
            tokens = line.split(" ")
            if len(tokens) != 3:
                raise ValueError(
                    "Invalid d4 format: AND node with wrong number of tokens")
            node_id = int(tokens[1])
            d4_graph[node_id] = D4Node(_D4_AND_NODE)
        elif line.startswith('f'):
            # FALSE NODE
            total_nodes += 1
            tokens = line.split(" ")
            if len(tokens) != 3:
                raise ValueError(
                    "Invalid d4 format: FALSE node with wrong number of tokens")
            node_id = int(tokens[1])
            d4_graph[node_id] = D4Node(_D4_FALSE_NODE)
        elif line.startswith('t'):
            # TRUE NODE
            total_nodes += 1
            tokens = line.split(" ")
            if len(tokens) != 3:
                raise ValueError(
                    "Invalid d4 format: TRUE node with wrong number of tokens")
            node_id = int(tokens[1])
            d4_graph[node_id] = D4Node(_D4_TRUE_NODE)
        elif line[0].isdigit():
            # ARC
            total_arcs += 1
            tokens = line.split(" ")
            if len(tokens) < 3:
                raise ValueError(
                    "Invalid d4 format: ARC with insufficient amount of tokens")
            src_id = int(tokens[0])  # source node
            dst_id = int(tokens[1])  # destination node
            label = list(map(int, tokens[2:]))
            # remove last item from label since it is the 0
            label.pop()
            d4_graph[src_id].add_edge(dst_id, label)

    # DFS TO COMPUTE FORMULA
    pysmt_node = d4_graph[1].to_pysmt(mapping, d4_graph)

    return pysmt_node, total_nodes, total_arcs


def count_nodes_and_edges_from_d4_nnf(d4_file: str) -> Tuple[int, int]:
    """
    Counts nodes and edges of the formula contained in the file d4_file from nnf format to a pysmt FNode

    Args:
        d4_file (str) -> the path to the file where the dimacs output needs to be saved

    Returns:
        (int,int) -> the total nodes and edges of the formula (#nodes,#edges)
    """
    total_nodes = 0
    total_edges = 0
    with open(d4_file, "r", encoding="utf8") as data:
        contents = data.read()
    lines: List[str] = contents.split("\n")
    lines = list(filter(lambda x: x != "", lines))
    for line in lines:
        if line.startswith('f') or line.startswith('o') or line.startswith('t') or line.startswith('a'):
            total_nodes += 1
        elif line[0].isdigit():
            total_edges += 1
    return (total_nodes, total_edges)


def from_d4_nnf_to_smtlib(
    d4_file: str, smtlib_file: str, mapping: Dict[int, FNode]
) -> None:
    """
    Translates the formula inside d4_file from nnf format to pysmt
    FNode and saves it in a SMT-Lib file.

    Args:
        d4_file (str) -> the path to the file where the dimacs output need to be saved
        smtlib_file (str) -> the path to a file that will be overwritten with the
            output SMT-Lib formula
        mapping (Dict[int,FNode]) -> a mapping that associates to integers a pysmt atom,
            used to translate the variables from their abstraction in the nnf format to pysmt
    """
    phi = from_d4_nnf_to_pysmt(d4_file, mapping)
    write_smtlib(phi, smtlib_file)


def compile_dDNNF(
        phi: FNode,
        tlemmas: List[FNode] | None = None,
        keep_temp: bool = False,
        tmp_path: str | None = None,
        computation_logger: Dict | None = None,
        verbose: bool = False,
        back_to_fnode: bool = True) -> Tuple[FNode | None, int, int]:
    """
    Compiles an FNode in dDNNF through the d4 compiler

    Args:
        phi (FNode) -> a pysmt formula
        tlemmas (List[FNode] | None) = None -> a list of theory lemmas to be added to the formula
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
    # check if d4 is available and executable
    if _D4_EXECUTABLE is None or not os.path.isfile(_D4_EXECUTABLE):
        raise FileNotFoundError(
            "The binary for the d4 compiler is missing. Please check the installation path and update the .env file.")
    if not os.access(_D4_EXECUTABLE, os.X_OK):
        raise PermissionError(
            "The d4 binary is not executable. Please check the permissions for the file and grant execution rights.")

    # failsafe for computation_logger
    if computation_logger is None:
        computation_logger = {}

    computation_logger["dDNNF compiler"] = "d4"

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
    mapping, quantified_vars = from_smtlib_to_dimacs_file(
        phi, f"{tmp_folder}/dimacs.cnf", tlemmas
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

    # call d4 for compilation
    # output should be in file temp_folder/compilation_output.nnf
    start_time = time.time()
    if verbose:
        print("Compiling dDNNF...")
    result = os.system(
        f"timeout 3600s {_D4_EXECUTABLE} -dDNNF {tmp_folder}/dimacs.cnf -out={tmp_folder}/compilation_output.nnf > /dev/null"
    )
    if result != 0:
        raise TimeoutError("d4 compilation failed: timeout")
    elapsed_time = time.time() - start_time
    computation_logger["dDNNF compilation time"] = elapsed_time
    if verbose:
        print(f"dDNNF compilation completed in {elapsed_time} seconds")

    # fix output
    _fix_ddnnf(f"{tmp_folder}/compilation_output.nnf",
               mapping, quantified_vars)

    # counting size
    nodes, edges = count_nodes_and_edges_from_d4_nnf(
        f"{tmp_folder}/compilation_output.nnf")

    # return if not back to fnode
    if not back_to_fnode:
        return None, nodes, edges

    # loading saved mapping
    # reverse_mapping = load_mapping(f"{tmp_folder}/mapping/mapping.json")

    # translate to pysmt
    start_time = time.time()
    if verbose:
        print("Translating to pysmt...")
    phi_ddnnf, nodes, edges = from_d4_nnf_to_pysmt(
        f"{tmp_folder}/compilation_output.nnf", reverse_mapping)
    if os.path.exists(tmp_folder) and not keep_temp:
        os.system(f"rm -rd {tmp_folder}")
    elapsed_time = time.time() - start_time
    computation_logger["pysmt translation time"] = elapsed_time
    if verbose:
        print(f"pysmt translation completed in {elapsed_time} seconds")
    return phi_ddnnf, nodes, edges


def load_dDNNF(nnf_path: str, mapping_path: str) -> FNode:
    """
    Load a dDNNF from file and translate it to pysmt

    Args:
        nnf_path (str) ->       the path to the file containing the dDNNF in 
                                NNF format provided by the d4 compiler
        mapping_path (str) ->   the path to the file containing the mapping

    Returns:
        (FNode) -> the pysmt formula translated from the dDNNF
    """
    mapping = load_mapping(mapping_path)
    return from_d4_nnf_to_pysmt(nnf_path, mapping)


def _fix_ddnnf(nnf_file: str, var_map: dict[FNode, int], projected_vars: set[FNode]):
    """
    Author: Masinag

    The d-DNNF output by d4 can contain variables that are not in the projected variables set.
    However, it should be safe to simply remove them from the d-DNNF file.

    Args:
        nnf_file (str) -> the path to the nnf file where the ddnnf is stored
        var_map (Dict[FNode,int]) -> a mapping between nodes and integers
        projected_vars (Set[Fnode]) -> the set of variables that have to be removed
    """
    with open(nnf_file, "r", encoding='utf8') as f:
        lines = f.readlines()

    projected_ids = {var_map[v] for v in projected_vars}
    ids_map = {v: i for i, v in enumerate(projected_ids, start=1)}

    with open(nnf_file, "w", encoding='utf8') as f:
        for line in lines:
            if m := _RE_NNF_EDGE.match(line):
                a, b, ll = m.groups()
                f.write(f"{a} {b}")
                for l in (ll or "").split():
                    i = int(l)
                    a = abs(i)
                    s = 1 if i > 0 else -1
                    if a in projected_ids:
                        f.write(f" {s * ids_map[a]}")
                f.write(" 0\n")
            else:
                f.write(line)


if __name__ == "__main__":
    from theorydd.formula import bottom, default_phi, read_phi
    test_phi = read_phi('input/shortest_path.smt')

    print(test_phi.serialize())

    _phi_ddnnf, _a, _b = compile_dDNNF(
        test_phi, None, back_to_fnode=False, verbose=True, keep_temp=True, tmp_path="tmp")
