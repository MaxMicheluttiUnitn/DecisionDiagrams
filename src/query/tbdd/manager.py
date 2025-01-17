"""module where all the queries functions are defined"""

import sys
import time
from typing import Dict, List

from pysmt.fnode import FNode

from theorydd.tdd.theory_bdd import TheoryBDD

from src.query.util import aliases_from_mapping,is_tbdd_loading_folder_correct
from src.query.query_interface import QueryInterface

class TBDDQueryManager(QueryInterface):
    """manager to handle all queries on T-BDDs"""

    loading_time: float

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
        # load tbdd from folder to subtract loading time from query time
        _tbdd = self._load_tbdd()
        self.loading_time = time.time() - start_time

    def _load_tbdd(self) -> TheoryBDD:
        """function to load the T-BDD from the source folder"""
        return TheoryBDD(None, folder_name=self.source_folder)

    def check_consistency(self) -> bool:
        """function to check if the encoded formula is consistent

        Returns:
            bool: True if the formula is consistent, False otherwise"""
        # load TBDD
        start_time = time.time()
        tbdd = self._load_tbdd()
        load_time = time.time() - start_time

        # check coinsistency
        is_sat = tbdd.is_sat()
        consistency_time = time.time() - start_time - load_time

        return is_sat

    def check_validity(self) -> bool:
        """function to check if the encoded formula is valid

        Returns:
            bool: True if the formula is valid, False otherwise"""
        # load TBDD
        start_time = time.time()
        tbdd = self._load_tbdd()
        load_time = time.time() - start_time

        # check validity
        is_valid = tbdd.is_valid()
        validity_time = time.time() - start_time - load_time

        return is_valid

    def _check_entail_clause_body(self, clause: FNode) -> bool:
        """function to check if the encoded formula entails the given clause

        Args:
            clause (FNode): the clause to check for entailment
        """
        # RETRIEVE THE INDEXES ON WHICH TO OPERATE
        clause_items = aliases_from_mapping(clause, self.abstraction_mapping)

        # NEGATE ALL ITEMS IN THE CLAUSE
        # TO OBTAIN A CUBE EQUIVALENT TO
        # NOT CLAUSE
        clause_items_negated = []
        for item in clause_items:
            if item.startswith('-'):
                clause_items_negated.append(item[1:])
            else:
                clause_items_negated.append('-' + item)

        # LOAD THE T-BDD
        start_time = time.time()
        tbdd = self._load_tbdd()
        load_time = time.time() - start_time

        # CONDITION OVER CLAUSE ITEMS NEGATED
        self._condition_tbdd(tbdd, clause_items_negated)
        # CHECK IF THE CONDITIONED T-BDD IS UNSAT
        consistency = tbdd.is_sat()
        # IF THE CONDITIONED T-BDD IS UNSAT, THEN THE FORMULA ENTAILS THE CLAUSE
        entailment = not consistency
        entailment_time = time.time() - start_time - load_time

        return entailment

    def _check_implicant_body(
            self,
            term: FNode) -> bool:
        """function to check if the term is an implicant for the encoded formula

        Args:
            term (FNode): the term to check
        """
        # RETRIEVE THE INDEX ON WHICH TO OPERATE
        term_index = aliases_from_mapping(term, self.abstraction_mapping)[0]

        # LOAD THE T-BDD
        start_time = time.time()
        tbdd = self._load_tbdd()
        load_time = time.time() - start_time

        # CONSTRUCT TBDD | term
        tbdd.condition(term_index)
        # CHECK IF THE CONDITIONED T-BDD IS VALID
        validity = tbdd.is_valid()
        # IF THE CONDITIONED T-BDD IS VALID, THEN THE TERM IS AN IMPLICANT
        implicant = validity
        implicant_time = time.time() - start_time - load_time

        return implicant

    def count_models(self) -> int:
        """function to count the number of models for the encoded formula

        Returns:
            int: the number of models for the encoded formula
        """
        # load TBDD
        start_time = time.time()
        tbdd = self._load_tbdd()
        load_time = time.time() - start_time

        # count models
        models_total = tbdd.count_models()
        # sometimes TBDD MC can return -1 due to memory issues
        if models_total == -1:
            print("Model counting Error", file=sys.stderr)
        counting_time = time.time() - start_time - load_time

        return models_total

    def enumerate_models(self) -> None:
        """function to enumerate all models for the encoded formula
        """
        # load TBDD
        start_time = time.time()
        tbdd = self._load_tbdd()
        load_time = time.time() - start_time

        for model in tbdd.pick_all_iter():
            print(model)
        enumeration_time = time.time() - start_time - load_time

    def _condition_body(
            self,
            alpha: FNode,
            output_file: str | None = None) -> None:
        """function to obtain [compiled formula | alpha], where alpha is a literal or a cube

        Args:
            alpha (FNode): the literal (or conjunction of literals) to condition the T-BDD
            output_file (str, optional): the path to the folder where the conditioned T-BDD will be saved. Defaults to None.
        """
        # RETRIEVE THE INDEXES ON WHICH TO OPERATE
        alpha_items = aliases_from_mapping(alpha, self.abstraction_mapping)

        # LOAD THE T-BDD
        start_time = time.time()
        tbdd = self._load_tbdd()
        load_time = time.time() - start_time

        # CONDITION THE T-BDD
        self._condition_tbdd(tbdd, alpha_items)
        conditioning_time = time.time() - start_time - load_time

        # SAVE CONDITIONED TBDD
        if output_file is not None:
            tbdd.save_to_folder(output_file)

    def _condition_tbdd(self, tbdd: TheoryBDD, items: List[str]) -> None:
        """function to condition the T-BDD with the given items

        Args:
            tbdd (TheoryBDD): the T-BDD to condition
            items (List[str]): the items to condition the T-BDD with
        """
        for item in items:
            tbdd.condition(item)

    def check_entail(self, data_folder: str) -> bool:
        """function to check entailment of the compiled formula with respect to the data in data_folder.
        The data in data folder must be of the correct format, which is the same of for the queried structure

        Args:
            data_folder (str): the path to the folder where the data is stored

        Returns:
            bool: True if the compiled formula entails the data, False otherwise
        """
        if not is_tbdd_loading_folder_correct(data_folder):
            raise ValueError("The data folder is not in the correct format for TBDDs")
        raise NotImplementedError()

    def conjunction(self, data_folder: str, output_path: str | None = None) -> None:
        """function to compute the conjunction of the compiled formula the data in data_folder.
        The data in data folder must be of the correct format, which is the same of for the queried structure

        Args:
            data_folder (str): the path to the folder where the data is stored
            output_path (str | None) [None]: the path to the file where the conjunction will be saved
        """
        if not is_tbdd_loading_folder_correct(data_folder):
            raise ValueError("The data folder is not in the correct format for TBDDs")
        raise NotImplementedError()

    def disjunction(self, data_folder: str, output_path: str | None = None) -> None:
        """function to compute the disjunction of the compiled formula the data in data_folder.
        The data in data folder must be of the correct format, which is the same of for the queried structure

        Args:
            data_folder (str): the path to the folder where the data is stored
            output_path (str | None) [None]: the path to the file where the disjunction will be saved
        """
        if not is_tbdd_loading_folder_correct(data_folder):
            raise ValueError("The data folder is not in the correct format for TBDDs")
        raise NotImplementedError()

    def negation(self, output_path: str | None = None) -> None:
        """function to compute the negation of the compiled formula

        Args:
            output_path (str | None) [None]: the path to the file where the negation will be saved
        """
        raise NotImplementedError()
