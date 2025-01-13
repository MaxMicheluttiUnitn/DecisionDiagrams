"""module where all the queries functions are defined"""

import time
from typing import Dict, List

from pysmt.fnode import FNode

from theorydd.tdd.theory_sdd import TheorySDD

from src.query.util import indexes_from_mapping
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

        start_time = time.time()
        self.tsdd = self._load_tsdd()
        self.loading_time = time.time() - start_time

    def _load_tsdd(self) -> TheorySDD:
        """function to load the T-SDD from the serialized files"""
        return TheorySDD(None, folder_name=self.source_folder)

    def check_consistency(self) -> bool:
        """function to check if the encoded formula is consistent

        Returns:
            bool: True if the formula is consistent, False otherwise"""
        # load TSDD
        start_time = time.time()
        tsdd = self._load_tsdd()
        load_time = time.time() - start_time

        # check consistency
        consistency = tsdd.is_sat()
        consistency_time = time.time() - start_time - load_time

        return consistency

    def check_validity(self):
        """function to check if the encoded formula is valid

        Returns:
            bool: True if the formula is valid, False otherwise"""
        # load TSDD
        start_time = time.time()
        tsdd = self._load_tsdd()
        load_time = time.time() - start_time

        # check validity
        validity = tsdd.is_valid()
        validity_time = time.time() - start_time - load_time

        return validity

    def _check_entail_clause_body(self, clause: FNode) -> bool:
        """function to check if the encoded formula entails the given clause

        Args:
            clause (FNode): the clause to check for entailment

        Returns:
            bool: True if the formula entails the clause, False otherwise
        """
        # RETRIEVE THE INDEXES ON WHICH TO OPERATE
        clause_items = indexes_from_mapping(clause, self.abstraction_mapping)

        clause_items_negated = [-item for item in clause_items]

        # LOAD THE T-SDD
        start_time = time.time()
        tsdd = self._load_tsdd()
        load_time = time.time() - start_time

        
        # CONDITION OVER CLAUSE ITEMS NEGATED
        self._condition_tsdd(tsdd, clause_items_negated)
        # CHECK IF THE CONDITIONED T-SDD IS UNSAT
        consistency = tsdd.is_sat()
        # IF THE CONDITIONED T-SDD IS UNSAT, THEN THE FORMULA ENTAILS THE CLAUSE
        entailment = not consistency
        entailment_time = time.time() - start_time - load_time

        return entailment

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
        term_index = indexes_from_mapping(term, self.abstraction_mapping)[0]
        
        # LOAD THE T-SDD
        start_time = time.time()
        tsdd = self._load_tsdd()
        load_time = time.time() - start_time

        # CONSTRUCT TSDD | term
        tsdd.condition(term_index)
        # CHECK IF THE CONDITIONED T-SDD IS VALID
        validity = tsdd.is_valid()
        # IF THE CONDITIONED T-SDD IS VALID, THEN THE TERM IS AN IMPLICANT
        implicant = validity
        implicant_time = time.time() - start_time - load_time

        return implicant

    def count_models(self) -> int:
        """function to count the number of models for the encoded formula

        Returns:
            int: the number of models for the encoded formula
        """
        start_time = time.time()
        tsdd = self._load_tsdd()
        load_time = time.time() - start_time

        # count models
        model_count = tsdd.count_models()
        model_count_time = time.time() - start_time - load_time

        return model_count

    def enumerate_models(self) -> None:
        """function to enumerate all models for the encoded formula"""
        start_time = time.time()
        tsdd = self._load_tsdd()
        load_time = time.time() - start_time

        # enumerate models
        models = tsdd.pick_all()
        for model in models:
            print(model)
        enumeration_time = time.time() - start_time - load_time

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
        alpha_items = indexes_from_mapping(alpha, self.abstraction_mapping)

        # LOAD THE T-BDD
        start_time = time.time()
        tsdd = self._load_tsdd()
        load_time = time.time() - start_time

        # CONDITION THE T-BDD
        self._condition_tsdd(tsdd, alpha_items)
        conditioning_time = time.time() - start_time - load_time

        # SAVE CONDITIONED TSDD
        if output_file is not None:
            tsdd.save_to_folder(output_file)

    def _condition_tsdd(self, tsdd: TheorySDD, items: List[str]) -> None:
        """function to condition the T-BDD with the given items

        Args:
            tbdd (TheoryBDD): the T-BDD to condition
            items (List[str]): the items to condition the T-BDD with
        """
        for item in items:
            tsdd.condition(item)
