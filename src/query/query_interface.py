"""interface for all Query objects"""

from abc import ABC, abstractmethod
from typing import Dict

from pysmt.fnode import FNode

from theorydd.solvers.mathsat_total import MathSATTotalEnumerator
from theorydd.formula import get_normalized, get_atoms, without_double_neg, read_phi

from src.query.util import is_clause, is_cube, is_term, normalize_refinement


class QueryInterface(ABC):
    """interface for all Query objects"""

    source_folder: str
    refinement_mapping: Dict[object, FNode]
    abstraction_mapping: Dict[FNode, object]
    # solver used for normalization of input
    normalizer_solver: MathSATTotalEnumerator

    def __init__(self,
                 source_folder: str,
                 refinement_mapping: Dict[object, FNode] | None = None,
                 abstraction_mapping: Dict[FNode, object] | None = None,
                 ):
        """
        initialize the query object.
        Always provide either the refinement_mapping or the abstraction_mapping or both when initializing the object,
        otherwise a ValueError will be raises

        Args:
            source_folder (str): the path to the folder where the serialized compiled formula is stored
            refinement_mapping (Dict[int, FNode]) [None]: the mapping of the indices on the compiled formula's abstraction to the atoms in its refinement
            abstraction_mapping (Dict[FNode, int]) [None]: the mapping of the atoms of the formula to the indices in the compiled formula's abstraction
        """
        self.source_folder = source_folder
        if refinement_mapping is None and abstraction_mapping is None:
            raise ValueError(
                "Either the refinement_mapping or the abstraction_mapping must be provided")
        if refinement_mapping is None:
            refinement_mapping = {v: k for k, v in abstraction_mapping.items()}

        # normalize atoms in the mapping
        self.normalizer_solver = MathSATTotalEnumerator()
        self.refinement_mapping = normalize_refinement(
            refinement_mapping, self.normalizer_solver)

        # compute reverse mapping to generate the abstraction funciton
        self.abstraction_mapping = {
            v: k for k, v in refinement_mapping.items()}

    @abstractmethod
    def check_consistency(self):
        """function to check if the encoded formula is consistent"""
        pass

    @abstractmethod
    def check_validity(self):
        """function to check if the encoded formula is valid"""
        pass

    def _clause_file_can_entail(self, clause_file: str) -> FNode:
        """checks if the provided input file can be used to check entailment

        raises exceptions if something is wrong with the file or its contents

        Args:
            clause_file (str): the path to the clause file

        Returns:
            (FNode): the correctly formatted clause provided as input"""
        # read data
        clause = read_phi(clause_file)

        # normalize the clause
        clause.simplify()
        clause = get_normalized(clause, self.normalizer_solver.get_converter())
        clause = without_double_neg(clause)

        if not is_term(clause) and not is_clause(clause):
            raise ValueError(
                "The clause must be a literal or a disjunction of literals")

        # check that the clause is on the same atoms as phi
        phi_atoms = set()
        for value in self.abstraction_mapping.keys():
            phi_atoms.add(get_atoms(value))
        phi_atoms = frozenset(phi_atoms)
        clause_atoms = frozenset(get_atoms(clause))
        if not phi_atoms.issuperset(clause_atoms):
            raise ValueError(
                "The clause must be on the same atoms as the encoded formula")
        return clause

    @abstractmethod
    def check_entail_clause(self, clause_file: str):
        """function to check if the encoded formula entails the clause specifoied in the clause_file

        Args:
            clause_file (str): the path to the smt2 file containing the clause to check
        """
        pass

    def _term_file_can_be_implicant(self, term_file: str) -> FNode:
        """checks if the provided input file can be used to query for implicant

        raises exceptions if something is wrong with the file or its contents

        Args:
            term_file (str): the path to the term file

        Returns:
            (FNode): the correctly formatted term provided as input"""
        term = read_phi(term_file)

        # normalize the term
        term.simplify()
        term = get_normalized(term, self.normalizer_solver.get_converter())
        term = without_double_neg(term)

        if not is_term(term):
            raise ValueError(
                "The term must be a literal which is an atom or a negated atom")

        # check that the term is on the same atoms as phi
        phi_atoms = set()
        for value in self.abstraction_mapping.keys():
            phi_atoms.add(get_atoms(value))
        phi_atoms = frozenset(phi_atoms)
        term_atom = get_atoms(term)[0]
        if term_atom not in phi_atoms:
            raise ValueError(
                "The clause must be on the same atoms as the encoded formula")

        return term

    @abstractmethod
    def check_implicant(
            self,
            term_file: str):
        """function to check if the term specified in term_file is an implicant for the encoded formula

        Args:
            term_file (str): the path to the smt2 file containing the term to check
        """
        pass

    @abstractmethod
    def count_models(self) -> int:
        """function to count the number of models for the encoded formula

        Returns:
            int: the number of models for the encoded formula
        """
        pass

    @abstractmethod
    def enumerate_models(self) -> None:
        """function to enumerate all models for the encoded formula
        """
        pass

    def _alpha_file_can_condition(self, alpha_file: str) -> FNode:
        """checks if the provided input file can be used to apply conditioning

        raises exceptions if something is wrong with the file or its contents

        Args:
            alpha_file (str): the path to the file where the conditioning atoms are specified

        Returns:
            (FNode): the correctly formatted cube provided as input"""
        alpha = read_phi(alpha_file)

        # normalize alpha
        alpha.simplify()
        alpha = get_normalized(alpha, self.normalizer_solver.get_converter())
        alpha = without_double_neg(alpha)

        if not is_term(alpha) and not is_cube(alpha):
            raise ValueError(
                "The alpha must be a literal or a conjunction of literals")

        # check that alpha is on the same atoms as phi
        phi_atoms = set()
        for value in self.abstraction_mapping.keys():
            phi_atoms.add(get_atoms(value))
        phi_atoms = frozenset(phi_atoms)
        alpha_atoms = frozenset(get_atoms(alpha))
        if not phi_atoms.issuperset(alpha_atoms):
            raise ValueError(
                "Alpha must be on the same atoms as the encoded formula")

        return alpha

    @abstractmethod
    def condition(
            self,
            alpha_file: str,
            output_file: str | None = None):
        """function to obtain [compiled formula | alpha], where alpha is a literal or a cube specified in the provided .smt2 file

        Args:
            alpha_file (str): the path to the smt2 file containing the literal (or conjunction of literals) to condition the compiled formula
            output_file (str | None) [None]: the path to the .smt2 file where the conditioned compiled formula will be saved. Defaults to None.
        """
        pass
