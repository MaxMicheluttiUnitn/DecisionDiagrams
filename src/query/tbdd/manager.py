"""module where all the queries functions are defined"""

import sys
import time
from typing import Dict, List, Tuple

from pysmt.fnode import FNode

from theorydd.tdd.theory_bdd import TheoryBDD

from src.query.util import aliases_from_mapping, is_tbdd_loading_folder_correct
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

        self.details["loading time"] = self.loading_time

    def _load_tbdd(self) -> TheoryBDD:
        """function to load the T-BDD from the source folder"""
        return TheoryBDD(None, folder_name=self.source_folder, solver=self.normalizer_solver)

    def _check_consistency(self) -> Tuple[bool, float]:
        """function to check if the encoded formula is consistent

        Returns:
            bool: True if the formula is consistent, False otherwise
            float: the structure loading time"""
        # load TBDD
        start_time = time.time()
        tbdd = self._load_tbdd()
        load_time = time.time() - start_time

        # check coinsistency
        is_sat = tbdd.is_sat()

        return is_sat, load_time

    def _check_validity(self) -> Tuple[bool, float]:
        """function to check if the encoded formula is valid

        Returns:
            bool: True if the formula is valid, False otherwise
            float: the structure loading time"""
        # load TBDD
        start_time = time.time()
        tbdd = self._load_tbdd()
        load_time = time.time() - start_time

        # check validity
        is_valid = tbdd.is_valid()

        return is_valid, load_time

    def _check_entail_clause_body(self, clause: FNode) -> Tuple[bool, float]:
        """function to check if the encoded formula entails the given clause

        Args:
            clause (FNode): the clause to check for entailment

        Returns:
            bool: True if the formula entails the clause, False otherwise
            float: the structure loading time
        """
        # RETRIEVE THE INDEXES ON WHICH TO OPERATE
        clause_aliases = aliases_from_mapping(clause, self.abstraction_mapping)

        clause_items = [(alias[1:] if alias.startswith('-') else alias, not alias.startswith('-')) for alias in clause_aliases]

        return self._check_entail_clause_random_body(clause_items)
    
    def _check_entail_clause_random_body(self, clause_items: List[Tuple[str,bool]]) -> Tuple[bool, float]:
        """function to check if the encoded formula entails the given clause

        Args:
            clause_items (List[Tuple[str,bool]]): the clause to check for entailment

        Returns:
            bool: True if the formula entails the clause, False otherwise
            float: the structure loading time
        """
        clause_items_negated = [(item[0], not item[1]) for item in clause_items]

        clause_items_negated_aliases = [(item[0] if item[1] else '-'+item[0]) for item in clause_items_negated]

        # LOAD THE T-BDD
        start_time = time.time()
        tbdd = self._load_tbdd()
        load_time = time.time() - start_time

        # CONDITION OVER CLAUSE ITEMS NEGATED
        self._condition_tbdd(tbdd, clause_items_negated_aliases)
        # CHECK IF THE CONDITIONED T-BDD IS UNSAT
        consistency = tbdd.is_sat()
        # IF THE CONDITIONED T-BDD IS UNSAT, THEN THE FORMULA ENTAILS THE CLAUSE
        entailment = not consistency

        return entailment, load_time
        

    def _check_implicant_body(
            self,
            term: FNode) -> Tuple[bool, float]:
        """function to check if the term is an implicant for the encoded formula

        Args:
            term (FNode): the term to check

        Returns:
            bool: True if the term is an implicant, False otherwise
            float: the structure loading time
        """
        # RETRIEVE THE INDEX ON WHICH TO OPERATE
        term_alias = aliases_from_mapping(term, self.abstraction_mapping)[0]

        term_item = (term_alias[1:] if term_alias.startswith('-') else term_alias, not term_alias.startswith('-'))

        return self._check_implicant_random_body(term_item)

    def _check_implicant_random_body(self, term_item: Tuple[str,bool]) -> Tuple[bool,float]:
        """function to check if the term is an implicant for the encoded formula
        
        Args:
            term_item (Tuple[str,bool]): the term to check
            
        Returns:
            bool: True if the term is an implicant, False otherwise
            float: the structure loading time
        """
        term_alias = term_item[0] if term_item[1] else "-"+term_item[0]

        # LOAD THE T-BDD
        start_time = time.time()
        tbdd = self._load_tbdd()
        load_time = time.time() - start_time

        # CONSTRUCT TBDD | term
        tbdd.condition(term_alias)
        # CHECK IF THE CONDITIONED T-BDD IS VALID
        validity = tbdd.is_valid()
        # IF THE CONDITIONED T-BDD IS VALID, THEN THE TERM IS AN IMPLICANT
        implicant = validity

        return implicant, load_time
        

    def _count_models(self) -> Tuple[int, float]:
        """function to count the number of models for the encoded formula

        Returns:
            int: the number of models for the encoded formula
            float: the structure loading time
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

        return models_total, load_time

    def _enumerate_models(self) -> float:
        """function to enumerate all models for the encoded formula

        Returns:
            float: the structure loading time
        """
        # load TBDD
        start_time = time.time()
        tbdd = self._load_tbdd()
        load_time = time.time() - start_time

        for model in tbdd.pick_all_iter():
            print(model)

        return load_time

    def _condition_body(
            self,
            alpha: FNode,
            output_file: str | None = None) -> float:
        """function to obtain [compiled formula | alpha], where alpha is a literal or a cube

        Args:
            alpha (FNode): the literal (or conjunction of literals) to condition the T-BDD
            output_file (str, optional): the path to the folder where the conditioned T-BDD will be saved. Defaults to None.

        Returns:
            float: the structure loading time
        """
        # RETRIEVE THE INDEXES ON WHICH TO OPERATE
        alpha_items = aliases_from_mapping(alpha, self.abstraction_mapping)

        # LOAD THE T-BDD
        start_time = time.time()
        tbdd = self._load_tbdd()
        load_time = time.time() - start_time

        # CONDITION THE T-BDD
        self._condition_tbdd(tbdd, alpha_items)

        # SAVE CONDITIONED TBDD
        if output_file is not None:
            tbdd.save_to_folder(output_file)

        return load_time

    def _condition_tbdd(self, tbdd: TheoryBDD, items: List[str]) -> None:
        """function to condition the T-BDD with the given items

        Args:
            tbdd (TheoryBDD): the T-BDD to condition
            items (List[str]): the items to condition the T-BDD with
        """
        for item in items:
            tbdd.condition(item)

    def _condition_random_body(self, cube_items: List[Tuple[str,bool]]) -> float:
        """function to condition the T-BDD with the given items

        Args:
            cube_items (List[str]): the items to condition the T-BDD with
        
        Returns:
            float: the structure loading
        """
        alpha_items = [item[0] if item[1] else '-'+item[0] for item in cube_items]

        # LOAD THE T-BDD
        start_time = time.time()
        tbdd = self._load_tbdd()
        load_time = time.time() - start_time

        # CONDITION THE T-BDD
        self._condition_tbdd(tbdd, alpha_items)

        return load_time

    def check_entail(self, data_folder: str) -> bool:
        """function to check entailment of the compiled formula with respect to the data in data_folder.
        The data in data folder must be of the correct format, which is the same of for the queried structure

        Args:
            data_folder (str): the path to the folder where the data is stored

        Returns:
            bool: True if the compiled formula entails the data, False otherwise
        """
        if not is_tbdd_loading_folder_correct(data_folder):
            raise ValueError(
                "The data folder is not in the correct format for TBDDs")
        raise NotImplementedError()

    def conjunction(self, data_folder: str, output_path: str | None = None) -> None:
        """function to compute the conjunction of the compiled formula the data in data_folder.
        The data in data folder must be of the correct format, which is the same of for the queried structure

        Args:
            data_folder (str): the path to the folder where the data is stored
            output_path (str | None) [None]: the path to the file where the conjunction will be saved
        """
        if not is_tbdd_loading_folder_correct(data_folder):
            raise ValueError(
                "The data folder is not in the correct format for TBDDs")
        raise NotImplementedError()

    def disjunction(self, data_folder: str, output_path: str | None = None) -> None:
        """function to compute the disjunction of the compiled formula the data in data_folder.
        The data in data folder must be of the correct format, which is the same of for the queried structure

        Args:
            data_folder (str): the path to the folder where the data is stored
            output_path (str | None) [None]: the path to the file where the disjunction will be saved
        """
        if not is_tbdd_loading_folder_correct(data_folder):
            raise ValueError(
                "The data folder is not in the correct format for TBDDs")
        raise NotImplementedError()

    def negation(self, output_path: str | None = None) -> None:
        """function to compute the negation of the compiled formula

        Args:
            output_path (str | None) [None]: the path to the file where the negation will be saved
        """
        raise NotImplementedError()
