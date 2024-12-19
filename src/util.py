"""utility functions for query_ddnnf"""
import os
from typing import Dict, List
from pysmt.fnode import FNode
from pysmt.shortcuts import Not
from theorydd.smt_solver import SMTSolver
from theorydd.formula import get_normalized, get_atoms


def is_tddnnf_loading_folder_correct(folder: str) -> bool:
    """checks if the folder where the dDNNF files are stored 
    has all the required content to load the T-dDNNF

    Args:
        folder (str): the path to the folder where the dDNNF files are stored

    Returns:
        bool: True if the folder has all required files and subfolders, False otherwise
    """
    # check that the folder exists
    if not os.path.exists(folder):
        return False
    # trim if path finishes with /
    if folder.endswith("/"):
        folder = folder[:-1]
    # check that mapping subfolder exists
    if not os.path.exists(os.path.join(folder, "/mapping")):
        return False
    # check that the mapping subfolder has a mapping.json file
    if not os.path.exists(os.path.join(folder, "/mapping/mapping.json")):
        return False
    # check that the file dimacs.cnf.nnf exists
    if not os.path.exists(os.path.join(folder, "/dimacs.cnf.nnf")):
        return False
    return True


def is_clause(clause: FNode) -> bool:
    """checks if the given formula is a clause

    Args:
        clause (FNode): the formula to check

    Returns:
        bool: True if the formula is a clause, False otherwise
    """
    if not clause.is_literal() or not clause.is_or():
        return False
    if clause.is_or():
        for arg in clause.args():
            if not is_term(arg):
                return False
    return True


def is_term(term: FNode) -> bool:
    """checks if the given formula is a term

    Args:
        term (FNode): the formula to check

    Returns:
        bool: True if the formula is a term, False otherwise
    """
    if not term.is_literal():
        return False
    return True


def is_negated(term: FNode) -> bool:
    """checks if the given formula is a negated term

    Args:
        term (FNode): the formula to check

    Returns:
        bool: True if the formula is a negated term, False otherwise
    """
    if not term.is_not():
        return False
    if not is_term(term.arg(0)):
        return False
    return True


def is_cube(phi: FNode) -> bool:
    """checks if the given formula is a cube

    Args:
        phi (FNode): the formula to check

    Returns:
        bool: True if the formula is a cube, False otherwise
    """
    if not phi.is_and():
        return False
    for arg in phi.args():
        if not is_term(arg):
            return False
    return True


def normalize_mapping(mapping: Dict[int, FNode], normalizer_solver: SMTSolver) -> Dict[int, FNode]:
    """normalizes the mapping of the variables to the indices in the dDNNF

    Args:
        mapping (Dict[int, FNode]): the mapping of the variables to the indices in the dDNNF
        normalizer_solver: the solver only used for the normalization of the mapping

    Returns:
        Dict[int, FNode]: the normalized mapping
    """
    normalized_mapping = {}
    for key, value in mapping.items():
        normalized_mapping[key] = get_normalized(
            value, normalizer_solver.get_converter())
        # if is_negated(normalized_mapping[key]):
        #     # I hope this never happens otherwise I may commit a crime
        #     raise NegatedMappingKeyException()
    return normalized_mapping


# class NegatedMappingKeyException(Exception):
#     """Exception raised when the mapping contains negated atoms"""

#     def __init__(self, message: str = "Mapping contains negated atoms!!!"):
#         super().__init__(message)


def indexes_from_mapping(mapping: Dict[FNode, int], phi: FNode) -> List[int]:
    """applyies the mapping to retrive the list of integer indexes,
    where a negative value implies a negated index

    Args:
        mapping (Dict[FNode,int]): a mapping from atoms to integers
        phi (FNode): a clause, cube or term formula

    Returns:
        (List[int]) : the list of corresponding indexes"""
    index_items = []
    if is_term(phi):
        index = 1
        atom = get_atoms(phi)[0]
        # check if the atom in the mapping is negated
        if atom not in mapping.keys():
            index = -1
            atom = Not(atom)
        index = index * mapping[atom]
        if is_negated(phi):
            index_items.append(-index)
        else:
            index_items.append(index)
    elif is_clause(phi) or is_cube(phi):
        for arg in phi.args():
            index = 1
            atom = get_atoms(arg)[0]
            # check if the atom in the mapping is negated
            if atom not in mapping.keys():
                index = -1
                atom = Not(atom)
            index = index * mapping[atom]
            if is_negated(arg):
                index_items.append(-index)
            else:
                index_items.append(index)
    else:
        raise ValueError("Cannot extract indexes from a formula which is not a cube, clause or term!")
    return index_items

def aliases_from_mapping(mapping: Dict[FNode, str], phi: FNode) -> List[str]:
    """applyies the mapping to retrieve the list of string aliases,
    where a string starting with "-" indicates a negated alias

    Args:
        mapping (Dict[FNode,str]): a mapping from atoms to strings
        phi (FNode): a clause, cube or term formula

    Returns:
        (List[str]) : the list of corresponding aliases"""
    alias_items = []
    if is_term(phi):
        alias_start = ""
        atom = get_atoms(phi)[0]
        # check if the atom in the mapping is negated
        if atom not in mapping.keys():
            alias_start = "-"
            atom = Not(atom)
        alias = alias_start + mapping[atom]
        if is_negated(phi):
            if alias.startswith("-"):
                alias_items.append(alias[1:])
            else:
                alias_items.append("-"+alias)
        else:
            alias_items.append(alias)
    elif is_clause(phi) or is_cube(phi):
        for arg in phi.args():
            alias_start = ""
            atom = get_atoms(arg)[0]
            # check if the atom in the mapping is negated
            if atom not in mapping.keys():
                alias_start = "-"
                atom = Not(atom)
            alias = alias_start + mapping[atom]
            if is_negated(arg):
                if alias.startswith("-"):
                    alias_items.append(alias[1:])
                else:
                    alias_items.append("-"+alias)
            else:
                alias_items.append(alias)
    else:
        raise ValueError("Cannot extract indexes from a formula which is not a cube, clause or term!")
    return alias_items
