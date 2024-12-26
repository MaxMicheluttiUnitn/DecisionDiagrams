"""module to handle the decision diagrams that need theory lemmas"""
import time
from typing import Dict, List

from pysmt.fnode import FNode
from pysmt.shortcuts import write_smtlib
from theorydd.tdd.theory_bdd import TheoryBDD
from theorydd.tdd.theory_sdd import TheorySDD
from theorydd.solvers.solver import SMTEnumerator
import theorydd.formula as formula

from src.kc.commands import Options
from src.kc.pysmt_c2d_middleware import C2DCompiler
from src.kc.pysmt_d4_middleware import D4Compiler



def theory_ddnnf(phi,
                 args: Options,
                 logger: Dict,
                 solver: SMTEnumerator,
                 tlemmas: List[FNode]):
    """theory dDNNF"""
    # THEORY dDNNF
    start_time = time.time()
    logger["T-dDNNF"] = {}
    ddnnf_compiler:str = args.dDNNF_compiler
    if args.verbose:
        print("T-dDNNF computation starting...")
    if ddnnf_compiler == "c2d":
        compiler = C2DCompiler()
    elif ddnnf_compiler == "d4":
        compiler = D4Compiler()
    else:
        raise ValueError("Invalid dDNNF compiler")
    try:
        tddnnf, nodes, edges = compiler.compile_dDNNF(
            phi,
            tlemmas,
            save_path=args.save_dDNNF,
            back_to_fnode=(not args.no_dDNNF_to_pysmt),
            verbose=args.verbose,
            computation_logger=logger["T-dDNNF"],
            timeout=args.dDNNF_timeout
        )
    except TimeoutError:
        if args.verbose:
            print("Timeout error in dDNNF computation")
        logger["timeout"] = "dDNNF"
        return
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
    if args.tdDNNF_output is not None and tddnnf is not None:
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
               solver: SMTEnumerator,
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
    if args.save_tbdd is not None:
        start_time = time.time()
        if args.verbose:
            print("Serializing T-BDD inside ", args.save_tbdd)
        tbdd.save_to_folder(args.save_tbdd)
        elapsed_time = time.time() - start_time
        logger["T-BDD"]["serialization time"] = elapsed_time
        if args.verbose:
            print("T-BDD serialization completed in ",
                  elapsed_time, " seconds")
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
        tbdd.graphic_dump(args.tbdd_output, dump_abstraction=args.dump_abstraction)
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
               solver: SMTEnumerator,
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
    if args.save_tsdd is not None:
        start_time = time.time()
        if args.verbose:
            print("Serializing T-SDD inside ", args.save_tsdd)
        tsdd.save_to_folder(args.save_tsdd)
        elapsed_time = time.time() - start_time
        logger["T-SDD"]["serialization time"] = elapsed_time
        if args.verbose:
            print("T-SDD serialization completed in ",
                  elapsed_time, " seconds")
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
        tsdd.graphic_dump(args.tsdd_output, dump_abstraction=args.dump_abstraction)
    if args.tvtree_output is not None:
        tsdd.graphic_dump_vtree(args.tvtree_output)
    if args.print_mapping:
        print(tsdd.get_mapping())
    del tsdd

    elapsed_time = time.time() - start_time
    logger["T-SDD"]["total DD computation time"] = elapsed_time
    if args.verbose:
        print("T-SDD computation completed in ",
              elapsed_time, " seconds")
