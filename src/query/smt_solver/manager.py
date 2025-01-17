"""module where all the queries functions are defined. These queries are executed through SMTsolver calls"""

import time

from pysmt.fnode import FNode
from pysmt.shortcuts import is_sat, Not, And

from theorydd.formula import read_phi as _get_phi, save_phi as _save_phi
from theorydd.solvers.mathsat_total import MathSATTotalEnumerator

from src.query.query_interface import QueryInterface


class SMTQueryManager(QueryInterface):
    """manager to handle all queries using a SMT solver"""

    loading_time: float

    def __init__(
            self,
            source_file: str):
        """
        initialize the manager with the path to the source file

        Args:
            source_file (str): the path to a smt or smt2 file where an SMT formula is defined
        """
        super().__init__(source_file, {}, {})

        start_time = time.time()
        _phi = _get_phi(source_file)
        self.loading_time = time.time() - start_time

    def check_consistency(self) -> bool:
        """function to check if the encoded formula is consistent

        Returns:
            bool: True if the formula is consistent, False otherwise"""
        # load phi
        start_time = time.time()
        phi = _get_phi(self.source_folder)
        load_time = time.time() - start_time

        # check coinsistency by calling SMT solver
        is_satisfiable = is_sat(phi, solver_name="msat")
        consistency_time = time.time() - start_time - load_time

        return is_satisfiable

    def check_validity(self) -> bool:
        """function to check if the encoded formula is valid

        Returns:
            bool: True if the formula is valid, False otherwise"""
        # load phi
        start_time = time.time()
        phi = _get_phi(self.source_folder)
        load_time = time.time() - start_time

        # check validity
        # if not phi is satisfiable, than the formula is not valid
        # this notion of validity is not completely
        # correct since we are checking boolean a validity
        # concept for a SMT formula
        is_valid = not is_sat(Not(phi), solver_name="msat")
        validity_time = time.time() - start_time - load_time

        return is_valid

    def _check_entail_clause_body(self, clause: FNode) -> bool:
        """function to check if the encoded formula entails the given clause

        Args:
            clause (FNode): the clause to check for entailment
        """
        # LOAD THE FORMULA
        start_time = time.time()
        phi = _get_phi(self.source_folder)
        load_time = time.time() - start_time

        # CHECK IF THE FORMULA ENTAILS THE CLAUSE
        # phi and not clause must be unsatisfiable
        entailment = not is_sat(And(phi, Not(clause)), solver_name="msat")
        entailment_time = time.time() - start_time - load_time

        return entailment

    def _check_implicant_body(
            self,
            term: FNode) -> bool:
        """function to check if the term is an implicant for the encoded formula

        Args:
            term (FNode): the term to check
        """
        # LOAD THE FORMULA
        start_time = time.time()
        phi = _get_phi(self.source_folder)
        load_time = time.time() - start_time

        # IMPLICANT = term -> phi
        # term and not phi must be unsatisfiable
        implicant = not is_sat(And(term, Not(phi)), solver_name="msat")
        implicant_time = time.time() - start_time - load_time

        return implicant

    def count_models(self) -> int:
        """function to count the number of models for the encoded formula

        Returns:
            int: the number of models for the encoded formula
        """
        # load phi
        start_time = time.time()
        phi = _get_phi(self.source_folder)
        load_time = time.time() - start_time

        # count models
        solver = MathSATTotalEnumerator()
        solver.check_all_sat(phi, boolean_mapping=None)
        models_total = len(solver.get_models())
        counting_time = time.time() - start_time - load_time

        return models_total

    def enumerate_models(self) -> None:
        """function to enumerate all models for the encoded formula
        """
        # load phi
        start_time = time.time()
        phi = _get_phi(self.source_folder)
        load_time = time.time() - start_time

        solver = MathSATTotalEnumerator()
        solver.check_all_sat(phi, boolean_mapping=None)
        models = solver.get_models()
        for model in models:
            print(model)
        enumeration_time = time.time() - start_time - load_time

    def _condition_body(
            self,
            alpha: FNode,
            output_file: str | None = None) -> None:
        """function to obtain [compiled formula | alpha], where alpha is a literal or a cube

        Args:
            alpha (FNode): the literal (or conjunction of literals) to condition the SMT formula
            output_file (str, optional): the path to the folder where the conditioned formula will be saved. Defaults to None.
        """
        # load phi
        start_time = time.time()
        phi = _get_phi(self.source_folder)
        load_time = time.time() - start_time

        # condition the formula
        conditioned_formula = And(phi, alpha)
        conditioning_time = time.time() - start_time - load_time

        # save the conditioned formula
        if output_file is not None:
            _save_phi(conditioned_formula, output_file)
