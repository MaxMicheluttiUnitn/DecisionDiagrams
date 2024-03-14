'''the main module for this project'''
# ADD these lines to .local/lib/python3.10/site-packages/pysmt/smtlib/parser/__init__.py
# to hide cython DeprecationWarning when importing module imp
#
# import warnings
# warnings.filterwarnings("ignore", category=DeprecationWarning)
import json
import time
from typing import Dict, List
import theorydd.formula as formula
from pysmt.fnode import FNode

from theorydd.smt_solver import SMTSolver
from theorydd.smt_solver_partial import PartialSMTSolver
from theorydd.lemma_extractor import extract

import abstraction_decision_diagrams as add
import theory_decision_diagrams as tdd
from commands import Options, get_args


def get_phi(args: Options, logger: Dict) -> FNode:
    """load the formula"""
    start_time = time.time()
    if args.verbose:
        print("Loading phi...")
    if args.input is None:
        phi = formula.default_phi()
    else:
        phi = formula.read_phi(args.input)
    elapsed_time = time.time() - start_time
    logger["phi loading time"] = elapsed_time
    if args.verbose:
        print("Loaded phi in ", elapsed_time, " seconds")
    return phi


def do_pure_abstraction(phi: FNode, args: Options, logger: Dict) -> None:
    """DO ALL FUNCTIONS THAT DO NOT REQUIRE All-SMT to be computed"""
    # ABSTRACTION BDD
    if args.abstraction_bdd:
        add.abstr_bdd(phi, args, logger)
    # ABSTRACTION SDD
    if args.abstraction_sdd:
        add.abstr_sdd(phi, args, logger)
    # LDD
    if args.ldd:
        add.ldd(phi, args, logger)
    # XSDD
    if args.xsdd:
        add.xsdd(phi, args, logger)


def dump_details(logger: Dict, args: Options) -> None:
    """dump details on file"""
    filename = args.details_file
    with open(filename, 'w', encoding='utf8') as f:
        json.dump(logger, f)


def load_details(args: Options) -> Dict:
    """load details from file"""
    filename = args.load_details
    logger = {}
    with open(filename, 'r', encoding='utf8') as f:
        logger = json.load(f)
    return logger


def get_solver(args: Options) -> SMTSolver | PartialSMTSolver:
    """returns the solver chosen by the user"""
    if args.solver == "total":
        return SMTSolver()
    else:
        return PartialSMTSolver()


def is_smt_phase_necessary(args: Options):
    """checks if the user necessitates to do the all-SMT phase"""
    return args.save_lemmas or args.tsdd or args.tbdd or args.print_lemmas or args.print_models


def smt_phase(phi: FNode, args: Options, logger: Dict):
    """SMT phase"""
    smt_solver = get_solver(args)

    tlemmas: List[FNode] | None = None
    if args.load_lemmas is None:
        # COMPUTE LEMMAS IF NECESSARY
        _sat, tlemmas, boolean_mapping = extract(
            phi,
            smt_solver,
            verbose=args.verbose,
            use_boolean_mapping=(~ args.no_boolean_mapping),
            computation_logger=logger)

        if args.count_models:
            models_total = len(smt_solver.get_models())
            logger["All-SMT models"] = models_total
            if args.verbose:
                print("All-SMT total models ", models_total)

        if args.print_models:
            print("All-SMT models:")
            models = smt_solver.get_models()
            if boolean_mapping is not None:
                counter = 0
                for model in models:
                    out = ""
                    for elem in model:
                        if elem.is_not():
                            out += str(boolean_mapping[elem.args()[0]]) + ", "
                        else:
                            out += str(boolean_mapping[elem]) + ", "
                    counter += 1
                    print(counter, ": [", out[:len(out)-2], "]", sep="")
            else:
                print("\n".join(map(str, models)))

        logger["total lemmas"] = len(tlemmas)
        if args.verbose:
            print("All-SMT found ", len(tlemmas), " theory lemmas")

        if args.print_lemmas:
            print("All-SMT lemmas:")
            print("\n".join(map(lambda x: x.serialize(), tlemmas)))

        # SAVE THE LEMMAS IF NECESSARY
        if args.save_lemmas is not None:
            if len(tlemmas) > 1:
                formula.save_phi(formula.big_and(tlemmas), args.save_lemmas)
            elif len(tlemmas) == 1:
                formula.save_phi(tlemmas[0], args.save_lemmas)
            else:
                formula.save_phi(formula.top(), args.save_lemmas)

    # T-BDD
    if args.tbdd:
        tdd.theory_bdd(phi, args, logger, smt_solver, tlemmas)

    # T-SDD
    if args.tsdd:
        tdd.theory_sdd(phi, args, logger, smt_solver, tlemmas)


def main() -> None:
    '''Main function for this project'''
    global_start_time = time.time()
    args = get_args()
    if args.verbose:
        print("Starting computation...")
    if args.load_details:
        logger = load_details(args)
        # in case of computation restarting, adjust start time accordingly
        if logger["total computation time"] is not None:
            global_start_time = global_start_time - \
                logger["total computation time"]
    else:
        logger = {}

    # LOAD FORMULA
    phi = get_phi(args, logger)

    # ONLY NEEDS ABSTRACTION
    do_pure_abstraction(phi, args, logger)

    # SMT PHASE (ONLY DONE IF NECESSARY)
    if is_smt_phase_necessary(args):
        smt_phase(phi, args, logger)

    global_elapsed_time = time.time() - global_start_time
    if args.verbose:
        print("All finished in ", global_elapsed_time, " seconds")
    logger['total computation time'] = global_elapsed_time
    if args.details_file is not None:
        dump_details(logger, args)


if __name__ == "__main__":
    main()
