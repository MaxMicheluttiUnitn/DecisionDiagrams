"""module where all the queries functions are defined"""

from typing import Dict
from pysmt.fnode import FNode
from theorydd.formula import read_phi, get_normalized, get_atoms, without_double_neg
from theorydd.smt_solver import SMTSolver
from src.util import is_clause, is_term, is_cube, indexes_from_mapping


def check_consistency(source_folder: str):
    """function to check if the encoded formula is consistent

    Args:
        source_folder (str): the path to the folder where the dDNNF files are stored
    """
    raise NotImplementedError()


def check_validity(source_folder: str):
    """function to check if the encoded formula is valid

    Args:
        source_folder (str): the path to the folder where the dDNNF files are stored
    """
    raise NotImplementedError()


def check_entail_clause(
        source_folder: str,
        refinement_mapping: Dict[int, FNode],
        abstraction_mapping: Dict[FNode, int],
        normalizer_solver: SMTSolver,
        clause_file: str):
    """function to check if the encoded formula entails the clause specifoied in the clause_file

    Args:
        source_folder (str): the path to the folder where the dDNNF files are stored
        refinement_mapping (Dict[int, FNode]): the mapping of the variables to the indices in the dDNNF
        normalizer_solver (SMTSolver): the solver only used for the normalization of the mapping   
        clause_file (str): the path to the smt2 file containing the clause to check
    """
    clause = read_phi(clause_file)

    # normalize the clause
    clause.simplify()
    clause = get_normalized(clause, normalizer_solver.get_converter())
    clause = without_double_neg(clause)

    if not is_term(clause) and not is_clause(clause):
        raise ValueError(
            "The clause must be a literal or a disjunction of literals")

    # check that the clause is on the same atoms as phi
    phi_atoms = set()
    for value in abstraction_mapping.keys():
        phi_atoms.add(get_atoms(value))
    phi_atoms = frozenset(phi_atoms)
    clause_atoms = frozenset(get_atoms(clause))
    if not phi_atoms.issuperset(clause_atoms):
        raise ValueError(
            "The clause must be on the same atoms as the encoded formula")

    # RETRIEVE THE INDEXES ON WHICH TO OPERATE
    clause_items = indexes_from_mapping(abstraction_mapping, clause)
    raise NotImplementedError()


def check_implicant(
        source_folder: str,
        refinement_mapping: Dict[int, FNode],
        abstraction_mapping: Dict[FNode, int],
        normalizer_solver: SMTSolver,
        term_file: str):
    """function to check if the term specified in term_file is an implicant for the encoded formula

    Args:
        source_folder (str): the path to the folder where the dDNNF files are stored
        refinement_mapping (Dict[int, FNode]): the mapping of the variables to the indices in the dDNNF
        abstraction_mapping (Dict[FNode, int]): the mapping of the indices on the DDNNF to the variables
        normalizer_solver (SMTSolver): the solver only used for the normalization of the mapping
        term_file (str): the path to the smt2 file containing the term to check
    """
    term = read_phi(term_file)

    # normalize the term
    term.simplify()
    term = get_normalized(term, normalizer_solver.get_converter())
    term = without_double_neg(term)

    if not is_term(term):
        raise ValueError(
            "The term must be a literal which is an atom or a negated atom")

    # check that the term is on the same atoms as phi
    phi_atoms = set()
    for value in abstraction_mapping.keys():
        phi_atoms.add(get_atoms(value))
    phi_atoms = frozenset(phi_atoms)
    term_atom = get_atoms(term)[0]
    if term_atom not in phi_atoms:
        raise ValueError(
            "The clause must be on the same atoms as the encoded formula")

    # RETRIEVE THE INDEX ON WHICH TO OPERATE
    term_index = indexes_from_mapping(abstraction_mapping, term)[0]

    raise NotImplementedError()


def count_models(source_folder: str) -> int:
    """function to count the number of models for the encoded formula

    Args:
        source_folder (str): the path to the folder where the dDNNF files are stored

    Returns:
        int: the number of models for the encoded formula
    """
    raise NotImplementedError()


def enumerate_models(source_folder: str, refinement_mapping: Dict[int, FNode]):
    """function to enumerate all models for the encoded formula

    Args:
        source_folder (str): the path to the folder where the dDNNF files are stored
        refinement_mapping (Dict[int, FNode]): the mapping of the variables to the indices in the dDNNF
    """
    raise NotImplementedError()


def condition_tddnnf(
        source_folder: str,
        refinement_mapping: Dict[int, FNode],
        abstraction_mapping: Dict[FNode, int],
        normalizer_solver: SMTSolver,
        alpha_file: str,
        output_file: str | None = None):
    """function to transform the T-dDNNF in T-dDNNF | alpha, where alpha is a literal or a cube specified in the provided .smt2 file

    Args:
        source_folder (str): the path to the folder where the dDNNF files are stored
        refinement_mapping (Dict[int, FNode]): the mapping of the variables to the indices in the dDNNF
        abstraction_mapping (Dict[FNode, int]): the mapping of the indices on the DDNNF to the variables
        normalizer_solver (SMTSolver): the solver only used for the normalization of the mapping
        alpha_file (str): the path to the smt2 file containing the literal (or conjunction of literals) to condition the T-dDNNF
        output_file (str, optional): the path to the .smt2 file where the conditioned T-dDNNF will be saved. Defaults to None.
    """
    alpha = read_phi(alpha_file)

    # normalize alpha
    alpha.simplify()
    alpha = get_normalized(alpha, normalizer_solver.get_converter())
    alpha = without_double_neg(alpha)

    if not is_term(alpha) and not is_cube(alpha):
        raise ValueError(
            "The alpha must be a literal or a conjunction of literals")

    # check that alpha is on the same atoms as phi
    phi_atoms = set()
    for value in abstraction_mapping.keys():
        phi_atoms.add(get_atoms(value))
    phi_atoms = frozenset(phi_atoms)
    alpha_atoms = frozenset(get_atoms(alpha))
    if not phi_atoms.issuperset(alpha_atoms):
        raise ValueError(
            "Alpha must be on the same atoms as the encoded formula")

    # RETRIEVE THE INDEXES ON WHICH TO OPERATE
    alpha_items = indexes_from_mapping(abstraction_mapping, alpha)

    raise NotImplementedError()
