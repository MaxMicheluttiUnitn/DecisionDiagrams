"""module to handle the decision diagrams that need theory lemmas"""
import time
from typing import Dict, List

from pysmt.fnode import FNode
from pysmt.shortcuts import write_smtlib
from theorydd.theory_bdd import TheoryBDD
from theorydd.theory_sdd import TheorySDD
from theorydd.smt_solver import SMTSolver
from theorydd.smt_solver_partial import PartialSMTSolver
import theorydd.formula as formula

from commands import Options
from pysmt_c2d_middleware import compile_dDNNF as compile_dDNNF_c2d
from pysmt_d4_middleware import compile_dDNNF as compile_dDNNF_d4



def theory_ddnnf(phi,
                 args: Options,
                 logger: Dict,
                 solver: SMTSolver | PartialSMTSolver,
                 tlemmas: List[FNode],
                 ddnnf_compiler:str = "c2d"):
    """theory dDNNF"""
    # THEORY dDNNF
    start_time = time.time()
    logger["T-dDNNF"] = {}
    if args.verbose:
        print("T-dDNNF computation starting...")
    if ddnnf_compiler == "c2d":
        if tlemmas is not None:
            phi_and_lemmas = formula.get_phi_and_lemmas(phi, tlemmas)
        else:
            tlemmas_big_and = formula.read_phi(args.load_lemmas)
            phi_and_lemmas = formula.get_phi_and_lemmas(phi, [tlemmas_big_and])
        phi_and_lemmas = formula.get_normalized(
            phi_and_lemmas, solver.get_converter())
        try:
            tddnnf, nodes, edges = compile_dDNNF_c2d(phi_and_lemmas,
                                                keep_temp=(
                                                    args.keep_c2d_temp is not None),
                                                verbose=args.verbose,
                                                computation_logger=logger["T-dDNNF"],
                                                tmp_path=args.keep_c2d_temp,
                                                back_to_fnode=(not args.no_dDNNF_to_pysmt))
        except TimeoutError:
            if args.verbose:
                print("Timeout error in dDNNF computation")
            logger["timeout"] = "dDNNF"
            return
    elif ddnnf_compiler == "d4":
        tddnnf, nodes, edges = compile_dDNNF_d4(phi,
                                                tlemmas,
                                                keep_temp=(
                                                    args.keep_c2d_temp is not None),
                                                verbose=args.verbose,
                                                computation_logger=logger["T-dDNNF"],
                                                tmp_path=args.keep_c2d_temp,
                                                back_to_fnode=(not args.no_dDNNF_to_pysmt))
    else:
        raise ValueError("Invalid ddnnf compiler")
    if args.count_nodes:
        if args.verbose:
            print("T-dDNNF Nodes: ", nodes)
        logger["T-dDNNF"]["nodes"] = nodes
    if args.count_vertices:
        if args.verbose:
            print("T-dDNNF Vertices: ", edges)
        logger["T-dDNNF"]["edges"] = edges
    if args.no_dDNNF_to_pysmt:
        return
    elapsed_time = time.time() - start_time
    logger["T-dDNNF"]["total computation time"] = elapsed_time
    if args.tdDNNF_output is not None:
        if args.verbose:
            print("Saving T-dDNNF to ", args.tdDNNF_output)
        write_smtlib(tddnnf, args.tdDNNF_output)
    if args.verbose:
        print("T-dDNNF computation completed in ",
              elapsed_time, " seconds")
    del tddnnf


def theory_bdd(phi,
               args: Options,
               logger: Dict,
               solver: SMTSolver | PartialSMTSolver,
               tlemmas: None | List[FNode]):
    """theory bdd"""
    # THEORY BDD
    start_time = time.time()
    logger["T-BDD"] = {}
    if args.verbose:
        print("T- BDD computation starting...")

    tbdd = TheoryBDD(phi,
                     solver=solver,
                     computation_logger=logger,
                     verbose=args.verbose,
                     tlemmas=tlemmas,
                     load_lemmas=args.load_lemmas)
    if args.count_nodes:
        nodes = tbdd.count_nodes()
        if args.verbose:
            print("Nodes: ", nodes)
        logger["T-BDD"]["DD nodes"] = nodes
    if args.count_vertices:
        vertices = tbdd.count_vertices()
        if args.verbose:
            print("Vertices: ", vertices)
        logger["T-BDD"]["DD vertices"] = vertices
    if args.count_models:
        models = tbdd.count_models()
        if args.verbose:
            print("Models: ", models)
        logger["T-BDD"]["DD models"] = models
    if args.tbdd_output is not None:
        tbdd.dump(args.tbdd_output, dump_abstraction=args.dump_abstraction)
    if args.print_mapping:
        print(tbdd.get_mapping())
    del tbdd

    elapsed_time = time.time() - start_time
    logger["T-BDD"]["total DD computation time"] = elapsed_time
    if args.verbose:
        print("T-BDD computation completed in ",
              elapsed_time, " seconds")


def theory_sdd(phi,
               args: Options,
               logger: Dict,
               solver: SMTSolver | PartialSMTSolver,
               tlemmas: None | List[FNode]):
    """theory sdd"""
    # THEORY SDD
    start_time = time.time()
    logger["T-SDD"] = {}
    if args.verbose:
        print("T-SDD computation starting...")

    tsdd = TheorySDD(phi,
                     solver=solver,
                     computation_logger=logger,
                     verbose=args.verbose,
                     vtree_type=args.tvtree,
                     tlemmas=tlemmas,
                     load_lemmas=args.load_lemmas)
    if args.count_nodes:
        nodes = tsdd.count_nodes()
        if args.verbose:
            print("Nodes: ", nodes)
        logger["T-SDD"]["DD nodes"] = nodes
    if args.count_vertices:
        vertices = tsdd.count_vertices()
        if args.verbose:
            print("Vertices: ", vertices)
        logger["T-SDD"]["DD vertices"] = vertices
    if args.count_models:
        models = tsdd.count_models()
        if args.verbose:
            print("Models: ", models)
        logger["T-SDD"]["DD models"] = models
    if args.tsdd_output is not None:
        tsdd.dump(args.tsdd_output, dump_abstraction=args.dump_abstraction)
    if args.tvtree_output is not None:
        tsdd.dump(args.tvtree_output)
    if args.print_mapping:
        print(tsdd.get_mapping())
    del tsdd

    elapsed_time = time.time() - start_time
    logger["T-SDD"]["total DD computation time"] = elapsed_time
    if args.verbose:
        print("T-SDD computation completed in ",
              elapsed_time, " seconds")
