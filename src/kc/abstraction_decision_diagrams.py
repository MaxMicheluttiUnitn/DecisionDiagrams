"""module to handle the decision diagrams that only need the abstraction"""
import time
from typing import Dict

from pysmt.shortcuts import write_smtlib

from theorydd.abstractdd.ldd import LDD as TheoryLDD
from theorydd.xsdd import TheoryXSDD
from theorydd.abstractdd.abstraction_bdd import AbstractionBDD
from theorydd.abstractdd.abstraction_sdd import AbstractionSDD

from src.kc.commands import Options
from src.kc.pysmt_c2d_middleware import C2DCompiler
from src.kc.pysmt_d4_middleware import D4Compiler


def abstr_ddnnf(phi, args: Options, logger: Dict):
    """abstraction dDNNF"""
    # ABSTRACTION dDNNF
    start_time = time.time()
    logger["Abstraction dDNNF"] = {}
    ddnnf_compiler:str = args.dDNNF_compiler
    if args.verbose:
        print("Abstraction dDNNF computation starting...")
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
            verbose=args.verbose,
            computation_logger=logger["Abstraction dDNNF"],
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
    if args.abstraction_dDNNF_output is not None and abs_ddnnf is not None:
        if args.verbose:
            print("Saving abstraction dDNNF to ",
                  args.abstraction_dDNNF_output)
        write_smtlib(abs_ddnnf, args.abstraction_dDNNF_output)
    del abs_ddnnf

    elapsed_time = time.time() - start_time
    logger["Abstraction dDNNF"]["total computation time"] = elapsed_time
    if args.verbose:
        print("Abstraction dDNNF computation completed in ",
              elapsed_time, " seconds")


def abstr_bdd(phi, args: Options, logger: Dict):
    """abstraction bdd"""
    # ABSTRACTION BDD
    start_time = time.time()
    logger["Abstraction BDD"] = {}
    if args.verbose:
        print("Abstraction BDD computation starting...")
    abdd = AbstractionBDD(phi, computation_logger=logger, verbose=args.verbose)
    if args.save_abstraction_bdd is not None:
        abdd.save_to_folder(args.save_abstraction_bdd)
    if args.count_nodes:
        nodes = abdd.count_nodes()
        if args.verbose:
            print("Nodes: ", nodes)
        logger["Abstraction BDD"]["DD nodes"] = nodes
    if args.count_vertices:
        vertices = abdd.count_vertices()
        if args.verbose:
            print("Vertices: ", vertices)
        logger["Abstraction BDD"]["DD vertices"] = vertices
    if args.count_models:
        models = abdd.count_models()
        if args.verbose:
            print("Models: ", models)
        logger["Abstraction BDD"]["DD models"] = models
    if args.abstraction_bdd_output is not None:
        abdd.graphic_dump(args.abstraction_bdd_output)
    del abdd

    elapsed_time = time.time() - start_time
    logger["Abstraction BDD"]["total DD computation time"] = elapsed_time
    if args.verbose:
        print("Abstraction BDD computation completed in ",
              elapsed_time, " seconds")


def abstr_sdd(phi, args: Options, logger: Dict):
    """abstraction sdd"""
    # ABSTRACTION SDD
    start_time = time.time()
    logger["Abstraction SDD"] = {}
    if args.verbose:
        print("Abstraction SDD computation starting...")

    asdd = AbstractionSDD(phi, computation_logger=logger,
                          verbose=args.verbose, vtree_type=args.abstraction_vtree)
    if args.save_abstraction_sdd is not None:
        asdd.save_to_folder(args.save_abstraction_sdd)
    if args.count_nodes:
        nodes = asdd.count_nodes()
        if args.verbose:
            print("Nodes: ", nodes)
        logger["Abstraction SDD"]["DD nodes"] = nodes
    if args.count_vertices:
        vertices = asdd.count_vertices()
        if args.verbose:
            print("Vertices: ", vertices)
        logger["Abstraction SDD"]["DD vertices"] = vertices
    if args.count_models:
        models = asdd.count_models()
        if args.verbose:
            print("Models: ", models)
        logger["Abstraction SDD"]["DD models"] = models
    if args.abstraction_sdd_output is not None:
        asdd.graphic_dump(args.abstraction_sdd_output)
    if args.abstraction_vtree_output is not None:
        asdd.graphic_dump_vtree(args.abstraction_vtree_output)
    del asdd

    elapsed_time = time.time() - start_time
    logger["Abstraction SDD"]["total DD computation time"] = elapsed_time
    if args.verbose:
        print("Abstraction SDD computation completed in ",
              elapsed_time, " seconds")


def ldd(phi, args: Options, logger: Dict):
    """ldd"""
    # LDD
    start_time = time.time()
    logger["LDD"] = {}
    if args.verbose:
        print("LDD computation starting...")

    ldd_obj = TheoryLDD(phi, args.ldd_theory,
                        verbose=args.verbose, computation_logger=logger)

    if args.ldd_output is not None:
        ldd_obj.dump(args.ldd_output)

    if args.count_nodes:
        nodes = ldd_obj.count_nodes()
        if args.verbose:
            print("Nodes: ", nodes)
        logger["LDD"]["DD nodes"] = nodes
    if args.count_vertices:
        vertices = ldd_obj.count_vertices()
        if args.verbose:
            print("Vertices: ", vertices)
        logger["LDD"]["DD vertices"] = vertices
    if args.count_models:
        models = ldd_obj.count_models()
        if args.verbose:
            print("Models: ", models)
        logger["LDD"]["DD models"] = models

    del ldd_obj

    elapsed_time = time.time() - start_time
    logger["LDD"]["total DD computation time"] = elapsed_time
    if args.verbose:
        print("LDD computation completed in ", elapsed_time, " seconds")


def xsdd(phi, args: Options, logger: Dict):
    """xsdd"""
    # XSDD
    # XSDD integration is weak because we realized early they
    # were not good for comparison with our approach
    start_time = time.time()
    logger["XSDD"] = {}
    if args.verbose:
        print("XSDD computation starting...")

    xsdd_obj = TheoryXSDD(phi, computation_logger=logger)
    del xsdd_obj

    elapsed_time = time.time() - start_time
    logger["XSDD"]["total DD computation time"] = elapsed_time
    if args.verbose:
        print("XSDD computation completed in ", elapsed_time, " seconds")
