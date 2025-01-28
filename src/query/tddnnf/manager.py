"""module where all the queries functions are defined"""

import os
import time
import subprocess
from typing import Dict, List

from pysmt.fnode import FNode


from src.query.util import indexes_from_mapping, UnsupportedQueryException, check_executable
from src.query.query_interface import QueryInterface
from src.query.constants import (
    DDNNF_CONDITION_PATH as _DDNNF_CONDITION_PATH,
    DECDNNF_PATH as _DECDNNF_PATH,
    CONDITION_DDNNF_OUTPUT_OPTION as _CONDITION_DDNNF_OUTPUT_OPTION,
    CONDITION_D4_OUTPUT_OPTION as _CONDITION_D4_OUTPUT_OPTION,
    TEPORARY_CONDITION_FILE as _TEMPORARY_CONDITIONED_FILE)


class DDNNFQueryManager(QueryInterface):
    """manager to handle all queries on T-dDNNF"""

    quantified_vars: set[int]
    total_vars: int
    output_option: str

    # IMPORTANT!
    # classes that inherit from this class must define this attribute
    d4_file: str

    def __init__(
            self,
            source_folder: str,
            ddnnf_vars: int,
            refinement_mapping: Dict[int, FNode] | None = None,
            abstraction_mapping: Dict[FNode, int] | None = None):
        """
        initialize the manager
        Always provide either the refinement_mapping or the abstraction_mapping or both when initializing the object,
        otherwise a ValueError will be raises

        Args:
            source_folder (str): the path to the folder where the serialized compiled formula is stored
            ddnnf_vars (int): the number of variables in the compiled formula (including the existentially quantified ones)
            refinement_mapping (Dict[int, FNode]) [None]: the mapping of the indices on the compiled formula's abstraction to the atoms in its refinement
            abstraction_mapping (Dict[FNode, int]) [None]: the mapping of the atoms of the formula to the indices in the compiled formula's abstraction
        """
        super().__init__(source_folder, refinement_mapping, abstraction_mapping)

        # check if the binaries are available
        check_executable(_DDNNF_CONDITION_PATH)
        check_executable(_DECDNNF_PATH)

        self.total_vars = ddnnf_vars
        self.output_option = _CONDITION_DDNNF_OUTPUT_OPTION

        # find the quantified variables by checking
        # which variables are not in the abstraction mapping keys
        self.quantified_vars = set()
        for i in range(1, ddnnf_vars+1):
            if i not in self.abstraction_mapping:
                self.quantified_vars.add(i)

        self.d4_file = ""

    def check_consistency(self) -> bool:
        """function to check if the encoded formula is consistent

        Returns:
            bool: True if the formula is consistent, False otherwise"""
        models = self._count_models(self.d4_file)
        result = (models > 0)

        return result

    def check_validity(self) -> bool:
        """function to check if the encoded formula is valid

        Returns:
            bool: True if the formula is valid, False otherwise"""
        models = self._count_models(self.d4_file)
        max_models = 2 ** len(self.abstraction_mapping)
        result = (models == max_models)

        return result

    def _check_entail_clause_body(self, clause: FNode) -> bool:
        """function to check if the encoded formula entails the clause

        Args:
            clause (FNode): an FNode representing the clause to check

        Returns:
            bool: True if the formula entails the clause, False otherwise
        """
        # RETRIEVE THE INDEXES ON WHICH TO OPERATE
        clause_items = indexes_from_mapping(clause, self.abstraction_mapping)

        # NEGATE ALL ITEMS IN THE CLAUSE
        # TO OBTAIN A CUBE EQUIVALENT TO
        # NOT CLAUSE
        clause_items_negated = []
        for item in clause_items:
            if item.startswith('-'):
                clause_items_negated.append(item[1:])
            else:
                clause_items_negated.append('-' + item)

        start_time = time.time()
        # CONDITION OVER CLAUSE ITEMS NEGATED
        self._condition_all_variables(
            clause_items_negated, _CONDITION_D4_OUTPUT_OPTION, _TEMPORARY_CONDITIONED_FILE)
        # COUNT MODELS OF CONDITIONED T-dDNNF
        conditioned_mc = self._count_models(_TEMPORARY_CONDITIONED_FILE)
        # IF THE CONDITIONED T-dDNNF HAS 0 MODELS, THEN THE FORMULA ENTAILS THE CLAUSE
        entailment = (conditioned_mc == 0)
        entailment_time = time.time() - start_time

        self._clear_tmp_file()

        return entailment

    def _clear_tmp_file(self) -> None:
        """function to clear the temporary file created during the execution"""
        if os.path.exists(_TEMPORARY_CONDITIONED_FILE):
            os.remove(_TEMPORARY_CONDITIONED_FILE)

    def _check_implicant_body(
            self,
            term: FNode) -> bool:
        """function to check if the term is an implicant for the encoded formula

        Args:
            term (FNode): the term to be checked
        """
        # RETRIEVE THE INDEX ON WHICH TO OPERATE
        term_index = indexes_from_mapping(term, self.abstraction_mapping)[0]

        start_time = time.time()
        # CONSTRUCT T-dDNNF | term
        self._condition_all_variables(
            [term_index], _CONDITION_D4_OUTPUT_OPTION, _TEMPORARY_CONDITIONED_FILE)
        # COUNT MODELS OF CONDITIONED T-dDNNF
        conditioned_mc = self._count_models(_TEMPORARY_CONDITIONED_FILE)
        # CHECK IF THE CONDITIONED T-dDNNF IS VALID (HAS 2**N MODELS)
        validity = (conditioned_mc == 2 ** len(self.abstraction_mapping))
        # IF THE CONDITIONED T-BDD IS VALID, THEN THE TERM IS AN IMPLICANT
        implicant = validity
        implicant_time = time.time() - start_time

        self._clear_tmp_file()

        return implicant

    def _count_models(self, input_file: str) -> int:
        """count_model body

        Args:
            input_file (str): the path to the input file for MC
        """
        try:
            process_data = subprocess.check_output(
                [_DECDNNF_PATH, "model-counting", "-i",
                    input_file, "--n-vars", self.total_vars],
                shell=True,
                text=True)
        except subprocess.CalledProcessError as e:
            raise RuntimeError(
                "An error occurred while counting the models") from e
        models_found = 0
        # find not empty output line that does not start with "["
        for line in process_data.split("\n"):
            if line and not line.startswith("["):
                models_found = int(line)
                break
        # remove quantified vars from the total number of models
        return models_found / (2 ** len(self.quantified_vars))

    def count_models(self) -> int:
        """function to count the number of models for the encoded formula

        Returns:
            int: the number of models for the encoded formula
        """
        start_time = time.time()
        result = self._count_models(self.d4_file)
        model_counting_time = time.time() - start_time
        return result

    def enumerate_models(self) -> None:
        """function to enumerate all models for the encoded formula
        """
        raise NotImplementedError()

    def _condition_all_variables(self, vars_to_condition: List[int], output_option: str | None = None, output_file: str | None = None) -> None:
        """function to condition the T-dDNNF on the specified variables

        Args:
            vars_to_condition (List[int]): the list of variables to condition on
            output_option (str): the option to pass to the T-dDNNF compiler for the output file
            output_file (str, optional): the path to the .smt2 file where the conditioned T-dDNNF will be saved. Defaults to None
        """
        if (len(vars_to_condition) == 0):
            raise ValueError("No variables to condition on")
        condition_option = "-c "
        for var in vars_to_condition:
            condition_option += str(var) + " "
        # trim the trailing space
        condition_option = condition_option[:-1]
        command = [_DDNNF_CONDITION_PATH, condition_option, "-i_d4",
                   self.d4_file, condition_option]
        if output_file is not None:
            if (output_option is None):
                # default output option
                output_option = _CONDITION_DDNNF_OUTPUT_OPTION
            command.append(self.output_option)
            command.append(output_file)
        try:
            _process_data = subprocess.check_output(
                command,
                shell=True,
                text=True)
        except subprocess.CalledProcessError as e:
            raise RuntimeError(
                "An error occurred while conditioning the T-dDNNF") from e

    def _condition_body(
            self,
            alpha: FNode,
            output_file: str | None = None) -> None:
        """function to obtain [compiled formula | alpha], where alpha is a literal or a cube

        Args:
            alpha (FNode): the literal (or conjunction of literals) to condition the T-dDNNF
            output_file (str, optional): the path to the .smt2 file where the conditioned T-dDNNF will be saved. Defaults to None.
        """
        # RETRIEVE THE INDEXES ON WHICH TO OPERATE
        alpha_items = indexes_from_mapping(alpha, self.abstraction_mapping)

        start_time = time.time()
        self._condition_all_variables(
            alpha_items, self.output_option, output_file)
        condition_time = time.time() - start_time

    def check_entail(self, data_folder: str) -> bool:
        """
        raises UnsupportedQueryException
        """

        raise UnsupportedQueryException(
            "T-dDNNF do not support polytime entailment checking")

    def conjunction(self, data_folder: str, output_path: str | None = None) -> None:
        """
        raises UnsupportedQueryException
        """
        raise UnsupportedQueryException(
            "T-dDNNF do not support polytime conjunction")

    def disjunction(self, data_folder: str, output_path: str | None = None) -> None:
        """
        raises UnsupportedQueryException
        """
        raise UnsupportedQueryException(
            "T-dDNNF do not support polytime disjunction")

    def negation(self, output_path: str | None = None) -> None:
        """
        raises UnsupportedQueryException
        """
        raise UnsupportedQueryException(
            "T-dDNNF do not support polytime negation")
