"""module to handle the decision diagrams that need theory lemmas"""
import time
import logging
from typing import Dict, List

from pysmt.fnode import FNode
from pysmt.shortcuts import write_smtlib
from theorydd.tdd.theory_bdd import TheoryBDD
from theorydd.tdd.theory_sdd import TheorySDD
from theorydd.solvers.solver import SMTEnumerator
from theorydd.ddnnf.c2d_compiler import C2DCompiler
from theorydd.ddnnf.d4_compiler import D4Compiler

from src.kc.commands import Options

kc_logger = logging.getLogger("knowledge_compiler")


def theory_ddnnf(phi,
                 args: Options,
                 data_logger: Dict,
                 solver: SMTEnumerator,
                 tlemmas: List[FNode],
                 sat_result: None | bool = None):
    """theory dDNNF"""
    # THEORY dDNNF
    start_time = time.time()
    data_logger["T-dDNNF"] = {}
    ddnnf_compiler: str = args.dDNNF_compiler
    kc_logger.info("T-dDNNF computation starting...")
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
            sat_result=sat_result,
            quantify_tseitsin=args.dDNNF_quantify_tseitsin,
            do_not_quantify=args.dDNNF_do_not_quantify,
            computation_logger=data_logger["T-dDNNF"],
            timeout=args.dDNNF_timeout
        )
    except TimeoutError:
        kc_logger.info("Timeout error in dDNNF computation")
        data_logger["timeout"] = "dDNNF"
        return
    if args.count_nodes:
        kc_logger.info("T-dDNNF Nodes: %s", str(nodes))
        data_logger["T-dDNNF"]["nodes"] = nodes
    if args.count_vertices:
        kc_logger.info("T-dDNNF Vertices: %s", str(edges))
        data_logger["T-dDNNF"]["edges"] = edges
    if args.no_dDNNF_to_pysmt:
        return
    elapsed_time = time.time() - start_time
    data_logger["T-dDNNF"]["total computation time"] = elapsed_time
    if args.tdDNNF_output is not None and tddnnf is not None:
        kc_logger.info("Saving T-dDNNF to %s", args.tdDNNF_output)
        write_smtlib(tddnnf, args.tdDNNF_output)
    kc_logger.info("T-dDNNF computation completed in %s seconds",
                   str(elapsed_time))
    del tddnnf


def theory_bdd(phi,
               args: Options,
               data_logger: Dict,
               solver: SMTEnumerator,
               tlemmas: None | List[FNode],
               sat_result: None | bool = None):
    """theory bdd"""
    # THEORY BDD
    start_time = time.time()
    data_logger["T-BDD"] = {}
    kc_logger.info("T- BDD computation starting...")

    tbdd = TheoryBDD(phi,
                     solver=solver,
                     computation_logger=data_logger,
                     tlemmas=tlemmas,
                     sat_result=sat_result,
                     load_lemmas=args.load_lemmas)
    if args.save_tbdd is not None:
        start_time = time.time()
        kc_logger.info("Serializing T-BDD inside %s", args.save_tbdd)
        tbdd.save_to_folder(args.save_tbdd)
        elapsed_time = time.time() - start_time
        data_logger["T-BDD"]["serialization time"] = elapsed_time
        kc_logger.info(
            "T-BDD serialization completed in %s seconds", str(elapsed_time))
    if args.count_nodes:
        nodes = tbdd.count_nodes()
        kc_logger.info("Nodes: %s", str(nodes))
        data_logger["T-BDD"]["DD nodes"] = nodes
    if args.count_vertices:
        vertices = tbdd.count_vertices()
        kc_logger.info("Vertices: %s", str(vertices))
        data_logger["T-BDD"]["DD vertices"] = vertices
    if args.count_models:
        models = tbdd.count_models()
        kc_logger.info("Models: %s", str(models))
        data_logger["T-BDD"]["DD models"] = models
    if args.tbdd_output is not None:
        tbdd.graphic_dump(args.tbdd_output,
                          dump_abstraction=args.dump_abstraction)
    if args.print_mapping:
        print(tbdd.get_mapping())
    del tbdd

    elapsed_time = time.time() - start_time
    data_logger["T-BDD"]["total DD computation time"] = elapsed_time
    kc_logger.info("T-BDD computation completed in %s seconds",
                   str(elapsed_time))


def theory_sdd(phi,
               args: Options,
               data_logger: Dict,
               solver: SMTEnumerator,
               tlemmas: None | List[FNode],
               sat_result: None | bool = None):
    """theory sdd"""
    # THEORY SDD
    start_time = time.time()
    data_logger["T-SDD"] = {}
    kc_logger.info("T-SDD computation starting...")
    tsdd = TheorySDD(phi,
                     solver=solver,
                     computation_logger=data_logger,
                     vtree_type=args.tvtree,
                     tlemmas=tlemmas,
                     sat_result=sat_result,
                     load_lemmas=args.load_lemmas)
    if args.save_tsdd is not None:
        start_time = time.time()
        kc_logger.info("Serializing T-SDD inside %s", args.save_tsdd)
        tsdd.save_to_folder(args.save_tsdd)
        elapsed_time = time.time() - start_time
        data_logger["T-SDD"]["serialization time"] = elapsed_time
        kc_logger.info(
            "T-SDD serialization completed in %s seconds", str(elapsed_time))
    if args.count_nodes:
        nodes = tsdd.count_nodes()
        kc_logger.info("Nodes: %s", str(nodes))
        data_logger["T-SDD"]["DD nodes"] = nodes
    if args.count_vertices:
        vertices = tsdd.count_vertices()
        kc_logger.info("Vertices: %s", str(vertices))
        data_logger["T-SDD"]["DD vertices"] = vertices
    if args.count_models:
        models = tsdd.count_models()
        kc_logger.info("Models: %s", str(models))
        data_logger["T-SDD"]["DD models"] = models
    if args.tsdd_output is not None:
        tsdd.graphic_dump(args.tsdd_output,
                          dump_abstraction=args.dump_abstraction)
    if args.tvtree_output is not None:
        tsdd.graphic_dump_vtree(args.tvtree_output)
    if args.print_mapping:
        print(tsdd.get_mapping())
    del tsdd

    elapsed_time = time.time() - start_time
    data_logger["T-SDD"]["total DD computation time"] = elapsed_time
    kc_logger.info("T-SDD computation completed in %s seconds",
                   str(elapsed_time))
