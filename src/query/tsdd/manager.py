"""module where all the queries functions are defined"""

from typing import Dict

from pysmt.fnode import FNode

from src.query.util import aliases_from_mapping
from src.query.query_interface import QueryInterface


class TSDDQueryManager(QueryInterface):
    """manager to handle all queries on T-SDDs"""

    def __init__(
            self,
            source_folder: str,
            refinement_mapping: Dict[str, FNode] | None = None,
            abstraction_mapping: Dict[FNode, str] | None = None):
        """
        initialize the manager
        Always provide either the refinement_mapping or the abstraction_mapping or both when initializing the object,
        otherwise a ValueError will be raises

        Args:
            source_folder (str): the path to the folder where the serialized compiled formula is stored
            refinement_mapping (Dict[int, FNode]) [None]: the mapping of the indices on the compiled formula's abstraction to the atoms in its refinement
            abstraction_mapping (Dict[FNode, int]) [None]: the mapping of the atoms of the formula to the indices in the compiled formula's abstraction
        """
        super().__init__(source_folder, refinement_mapping, abstraction_mapping)

    def check_consistency(self) -> bool:
        """function to check if the encoded formula is consistent
        
        Returns:
            bool: True if the formula is consistent, False otherwise"""
        raise NotImplementedError()

    def check_validity(self):
        """function to check if the encoded formula is valid
        
        Returns:
            bool: True if the formula is valid, False otherwise"""
        raise NotImplementedError()

    def _check_entail_clause_body(self, clause: FNode) -> bool:
        """function to check if the encoded formula entails the given clause

        Args:
            clause (FNode): the clause to check for entailment

        Returns:
            bool: True if the formula entails the clause, False otherwise
        """
        # RETRIEVE THE INDEXES ON WHICH TO OPERATE
        clause_items = aliases_from_mapping(clause, self.abstraction_mapping)
        raise NotImplementedError()

    def _check_implicant_body(
            self,
            term: FNode) -> bool:
        """function to check if the term is an implicant for the encoded formula

        Args:
            term (FNode): the term to check

        Returns:
            bool: True if the term is an implicant, False otherwise
        """
        # RETRIEVE THE INDEX ON WHICH TO OPERATE
        term_index = aliases_from_mapping(term, self.abstraction_mapping)[0]
        raise NotImplementedError()
    
    def count_models(self) -> int:
        """function to count the number of models for the encoded formula

        Returns:
            int: the number of models for the encoded formula
        """
        pass

    def enumerate_models(self) -> None:
        """function to enumerate all models for the encoded formula"""
        pass

    def _condition_body(
            self,
            alpha: FNode,
            output_file: str | None = None) -> None:
        """function to obtain [compiled formula | alpha], where alpha is a literal or a cube

        Args:
            alpha (FNode): the literal (or conjunction of literals) to condition the T-SDD
            output_file (str, optional): the path to the .smt2 file where the conditioned T-SDD will be saved. Defaults to None.
        """
        # RETRIEVE THE INDEXES ON WHICH TO OPERATE
        alpha_items = aliases_from_mapping(alpha, self.abstraction_mapping)

        raise NotImplementedError()
