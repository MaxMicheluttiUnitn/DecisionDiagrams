'''this module builds and handles DDs from pysmt formulas'''
from typing import List
from pysmt.fnode import FNode
from formula import get_phi
from theory_bdd import compute_bdd_cudd
from theory_sdd import compute_sdd as _compute_sdd
from theory_xsdd import compute_xsdd as _compute_xsdd
from theory_ldd import compute_ldd as _compute_ldd


def compute_xsdd(phi: FNode, computation_logger: any = {}):
    '''computing xsdd'''
    _compute_xsdd(phi, computation_logger)


def compute_sdd(phi: FNode,
                vtree_type: str = None,
                output_file: str = None,
                vtree_output: str = None,
                dump_abstraction: bool = False,
                print_mapping: bool = False,
                count_models: bool = False,
                count_nodes: bool = False,
                qvars: List[FNode] = [],
                computation_logger: any = {}) -> None:
    ' ' 'Computes the SDD for the boolean formula phi and saves it on a file' ' '
    _compute_sdd(phi, vtree_type, output_file, vtree_output, dump_abstraction,
                 print_mapping, count_models, count_nodes, qvars, computation_logger)


def compute_bdd(phi: FNode, output_file=None, dump_abstraction=False, print_mapping=False, computation_logger: any = {}) -> None:
    '''Computes the BDD for the boolean formula phi and saves it on a file using dd.autoref'''
    # For now always use compute_bdd_cudd
    return compute_bdd_cudd(phi, output_file, dump_abstraction, print_mapping, computation_logger=computation_logger)

def compute_ldd(phi: FNode,
                     output_file: str | None = None,
                     count_nodes:bool = False,
                     computation_logger: any = {}):
    '''Computes the LDD for the boolean formula phi and saves it on a file'''
    _compute_ldd(phi,output_file,count_nodes,computation_logger)

if __name__ == "__main__":
    test_phi = get_phi()
    # compute_bdd(test_phi)
    # compute_sdd(test_phi)
