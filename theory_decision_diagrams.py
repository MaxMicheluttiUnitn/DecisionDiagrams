"""module to handle the decision diagrams that only need the abstraction"""
import time
from typing import Dict

from theorydd.theory_ldd import TheoryLDD
from theorydd.theory_xsdd import TheoryXSDD
from theorydd.theory_bdd import TheoryBDD
from theorydd.theory_sdd import TheorySDD

from commands import Options


def theory_bdd(phi, args: Options, logger: Dict):
    """theory bdd"""
    # THEORY BDD
    start_time = time.time()
    logger["T-BDD"] = {}
    if args.verbose:
        print("T- BDD computation starting...")

    tbdd = TheoryBDD(phi, computation_logger=logger, verbose=args.verbose)
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
    if args.abstraction_bdd_output is not None:
        tbdd.dump(args.abstraction_bdd_output)
    del tbdd

    elapsed_time = time.time() - start_time
    logger["T-BDD"]["total DD computation time"] = elapsed_time
    if args.verbose:
        print("T-BDD computation completed in ",
              elapsed_time, " seconds")


def theory_sdd(phi, args: Options, logger: Dict):
    """theory sdd"""
    # THEORY SDD
    start_time = time.time()
    logger["T-SDD"] = {}
    if args.verbose:
        print("T-SDD computation starting...")

    tsdd = TheorySDD(phi, computation_logger=logger,
                     verbose=args.verbose, vtree_type=args.abstraction_vtree)
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
    if args.abstraction_sdd_output is not None:
        tsdd.dump(args.abstraction_sdd_output)
    if args.abstraction_vtree_output is not None:
        tsdd.dump(args.abstraction_vtree_output)
    del tsdd

    elapsed_time = time.time() - start_time
    logger["T-SDD"]["total DD computation time"] = elapsed_time
    if args.verbose:
        print("T-SDD computation completed in ",
              elapsed_time, " seconds")
