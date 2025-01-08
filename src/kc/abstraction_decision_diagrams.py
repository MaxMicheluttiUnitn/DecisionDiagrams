"""module to handle the decision diagrams that only need the abstraction"""
import logging
import time
from typing import Dict

from pysmt.shortcuts import write_smtlib

from theorydd.abstractdd.ldd import LDD as TheoryLDD
from theorydd.xsdd import TheoryXSDD
from theorydd.abstractdd.abstraction_bdd import AbstractionBDD
from theorydd.abstractdd.abstraction_sdd import AbstractionSDD
from theorydd.ddnnf.c2d_compiler import C2DCompiler
from theorydd.ddnnf.d4_compiler import D4Compiler

from src.kc.commands import Options

kc_logger = logging.getLogger("knowledge_compiler")


def abstr_ddnnf(phi, args: Options, data_logger: Dict):
    """abstraction dDNNF"""
    # ABSTRACTION dDNNF
    start_time = time.time()
    data_logger["Abstraction dDNNF"] = {}
    ddnnf_compiler: str = args.dDNNF_compiler
    kc_logger.info("Abstraction dDNNF computation starting...")
    if ddnnf_compiler == "c2d":
        compiler = C2DCompiler()
    elif ddnnf_compiler == "d4":
        compiler = D4Compiler()
    else:
        raise ValueError("Invalid dDNNF compiler")
    try:
        abs_ddnnf, nodes, edges = compiler.compile_dDNNF(
            phi,
            tlemmas=None,
            save_path=args.save_dDNNF,
            back_to_fnode=(not args.no_dDNNF_to_pysmt),
            computation_logger=data_logger["Abstraction dDNNF"],
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
    if args.abstraction_dDNNF_output is not None and abs_ddnnf is not None:
        kc_logger.info("Saving abstraction dDNNF to %s",
                       args.abstraction_dDNNF_output)
        write_smtlib(abs_ddnnf, args.abstraction_dDNNF_output)
    del abs_ddnnf

    elapsed_time = time.time() - start_time
    data_logger["Abstraction dDNNF"]["total computation time"] = elapsed_time
    kc_logger.info(
        "Abstraction dDNNF computation completed in %s seconds", str(elapsed_time))


def abstr_bdd(phi, args: Options, data_logger: Dict):
    """abstraction bdd"""
    # ABSTRACTION BDD
    start_time = time.time()
    data_logger["Abstraction BDD"] = {}
    kc_logger.info("Abstraction BDD computation starting...")
    abdd = AbstractionBDD(phi, computation_logger=data_logger)
    if args.save_abstraction_bdd is not None:
        abdd.save_to_folder(args.save_abstraction_bdd)
    if args.count_nodes:
        nodes = abdd.count_nodes()
        kc_logger.info("Nodes: %s", str(nodes))
        data_logger["Abstraction BDD"]["DD nodes"] = nodes
    if args.count_vertices:
        vertices = abdd.count_vertices()
        kc_logger.info("Vertices: %s", str(vertices))
        data_logger["Abstraction BDD"]["DD vertices"] = vertices
    if args.count_models:
        models = abdd.count_models()
        kc_logger.info("Models: %s", str(models))
        data_logger["Abstraction BDD"]["DD models"] = models
    if args.abstraction_bdd_output is not None:
        abdd.graphic_dump(args.abstraction_bdd_output)
    del abdd

    elapsed_time = time.time() - start_time
    data_logger["Abstraction BDD"]["total DD computation time"] = elapsed_time
    kc_logger.info("Abstraction BDD computation completed in %s seconds", str(elapsed_time))


def abstr_sdd(phi, args: Options, data_logger: Dict):
    """abstraction sdd"""
    # ABSTRACTION SDD
    start_time = time.time()
    data_logger["Abstraction SDD"] = {}
    kc_logger.info("Abstraction SDD computation starting...")

    asdd = AbstractionSDD(phi, computation_logger=data_logger,
                          vtree_type=args.abstraction_vtree)
    if args.save_abstraction_sdd is not None:
        asdd.save_to_folder(args.save_abstraction_sdd)
    if args.count_nodes:
        nodes = asdd.count_nodes()
        kc_logger.info("Nodes: %s", str(nodes))
        data_logger["Abstraction SDD"]["DD nodes"] = nodes
    if args.count_vertices:
        vertices = asdd.count_vertices()
        kc_logger.info("Vertices: %s", str(vertices))
        data_logger["Abstraction SDD"]["DD vertices"] = vertices
    if args.count_models:
        models = asdd.count_models()
        kc_logger.info("Models: %s", str(models))
        data_logger["Abstraction SDD"]["DD models"] = models
    if args.abstraction_sdd_output is not None:
        asdd.graphic_dump(args.abstraction_sdd_output)
    if args.abstraction_vtree_output is not None:
        asdd.graphic_dump_vtree(args.abstraction_vtree_output)
    del asdd

    elapsed_time = time.time() - start_time
    data_logger["Abstraction SDD"]["total DD computation time"] = elapsed_time
    kc_logger.info("Abstraction SDD computation completed in %s seconds", str(elapsed_time))


def ldd(phi, args: Options, data_logger: Dict):
    """ldd"""
    # LDD
    start_time = time.time()
    data_logger["LDD"] = {}
    kc_logger.info("LDD computation starting...")

    ldd_obj = TheoryLDD(phi, args.ldd_theory, computation_logger=data_logger)

    if args.ldd_output is not None:
        ldd_obj.dump(args.ldd_output)

    if args.count_nodes:
        nodes = ldd_obj.count_nodes()
        kc_logger.info("Nodes: %s", str(nodes))
        data_logger["LDD"]["DD nodes"] = nodes
    if args.count_vertices:
        vertices = ldd_obj.count_vertices()
        kc_logger.info("Vertices: %s", str(vertices))
        data_logger["LDD"]["DD vertices"] = vertices
    if args.count_models:
        models = ldd_obj.count_models()
        kc_logger.info("Models: %s", str(models))
        data_logger["LDD"]["DD models"] = models

    del ldd_obj

    elapsed_time = time.time() - start_time
    data_logger["LDD"]["total DD computation time"] = elapsed_time
    kc_logger.info("LDD computation completed in %s seconds", str(elapsed_time))


def xsdd(phi, args: Options, data_logger: Dict):
    """xsdd"""
    # XSDD
    # XSDD integration is weak because we realized early they
    # were not good for comparison with our approach
    start_time = time.time()
    data_logger["XSDD"] = {}
    kc_logger.info("XSDD computation starting...")

    xsdd_obj = TheoryXSDD(phi, computation_logger=data_logger)
    del xsdd_obj

    elapsed_time = time.time() - start_time
    data_logger["XSDD"]["total DD computation time"] = elapsed_time
    kc_logger.info("XSDD computation completed in %s seconds", str(elapsed_time))
