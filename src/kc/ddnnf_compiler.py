"""interface for ddnnf compiler implementations"""

from abc import ABC, abstractmethod
from typing import Dict, List, Tuple

from pysmt.fnode import FNode
from theorydd.formula import save_phi


class DDNNFCompiler(ABC):
    """interface for ddnnf compiler implementations"""
    abstraction: Dict[FNode, int]
    refinement: Dict[int, FNode]

    def __init__(self):
        self.abstraction = {}
        self.refinement = {}

    @abstractmethod
    def compile_dDNNF(
        self,
        phi: FNode,
        tlemmas: List[FNode] | None = None,
        save_path: str | None = None,
        back_to_fnode: bool = False,
        verbose: bool = False,
        computation_logger: Dict | None = None,
        timeout: int = 3600
    ) -> Tuple[FNode | None, int, int]:
        """compile the ddnnf of the formula phi with the given tlemmas.

        Raises a TimeoutError if the computation takes more than timeout seconds.

        Args:
            phi (FNode) -> a pysmt formula
            tlemmas (List[FNode] | None) = None -> a list of theory lemmas to be added to the formula
            save_path (str | None) = None -> the path where dDNNF data will be saved. 
                If it is set to None a random temporary folder starting with temp_ will be created
                and deleted once the comèputation ends
            computation_logger (Dict | None) = None -> a dictionary that will be filled with
                data about the computation
            verbose (bool) = False -> set it to True to print information about the computation
            back_to_fnode (bool) = True -> set it to False to avoid the final pysmt translation
            timeout (int) = 3600 -> the maximum time in seconds the computation is allowed to run

        Returns:
            Tuple[FNode | None, int, int] -> the dDNNF formula, the number of nodes and the number of edges"""
        pass

    @abstractmethod
    def from_smtlib_to_dimacs_file(
            self,
            phi: FNode,
            dimacs_file: str,
            tlemmas: List[FNode] | None = None) -> None:
        """convert a smtlib formula to a dimacs file

        Args:
            phi (FNode) -> the formula to be converted
            dimacs_file (str) -> the path to the file where the dimacs output need to be saved
            tlemmas (List[FNode] | None) = None -> a list of theory lemmas to be added to the formula
        """
        pass

    @abstractmethod
    def from_nnf_to_pysmt(
            self,
            nnf_file: str) -> Tuple[FNode, int, int]:
        """convert a ddnnf compilation output file to a pysmt formula.

        Args:
            nnf_file (str) -> the path to the file containing the ddnnf compilation output

        Returns:
            Tuple[FNode,int,int] -> the pysmt formula, the number of nodes and the number of edges"""
        pass

    @abstractmethod
    def count_nodes_and_edges_from_nnf(
            self,
            nnf_file: str) -> Tuple[int, int]:
        """count the number of nodes and edges in a ddnnf compilation ouput file

        Args:
            nnf_file (str) -> the path to the file containing the ddnnf compilation output"""
        pass

    def from_nnf_to_smtlib(
            self,
            nnf_file: str,
            smtlib_file: str) -> None:
        """
        Translates the formula inside nnf_file from nnf format to pysmt
        FNode and saves it in a SMT-Lib file.

        Args:
            nnf_file (str) -> the path to the file where the dimacs output need to be saved
            smtlib_file (str) -> the path to a file that will be overwritten with the
                output SMT-Lib formula
        """
        phi = self.from_nnf_to_pysmt(nnf_file)
        save_phi(phi, smtlib_file)

    def write_dimacs_true(self, dimacs_file: str) -> None:
        """writes the equivalent of a valid formula in a dimacs file"""
        with open(dimacs_file, "w", encoding="utf8") as dimacs_out:
            dimacs_out.write("p cnf 1 1\n1 -1 0\n")

    def write_dimacs_false(self, dimacs_file: str) -> None:
        """writes the equivalent of a unsatisfiable formula in a dimacs file"""
        with open(dimacs_file, "w", encoding="utf8") as dimacs_out:
            dimacs_out.write("p cnf 1 1\n1 -1 0\n")

    def write_dimacs(self, dimacs_file: str, phi_cnf: FNode, important_atoms_labels: List[int] | None = None) -> None:
        """writes the equivalent of a formula in a dimacs file"""
        total_variables = len(self.abstraction.keys())
        clauses: List[FNode] = phi_cnf.args()
        total_clauses = len(clauses)
        with open(dimacs_file, "w", encoding="utf8") as dimacs_out:
            # first line
            dimacs_out.write(f"p cnf {total_variables} {total_clauses}\n")
            # second line
            if important_atoms_labels is not None:
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
                                str(self.abstraction[negated_literal] * -1))
                        else:
                            translated_literals.append(
                                str(self.abstraction[literal]))
                    line = " ".join(translated_literals)
                elif clause.is_not():
                    negated_literal: FNode = clause.arg(0)
                    line = str(self.abstraction[negated_literal] * -1)
                else:
                    line = str(self.abstraction[clause])
                dimacs_out.write(line)
                dimacs_out.write(" 0\n")
