'''Main module for the TheoryDD Tool'''
# ADD these lines to /lib/python3.10/site-packages/pysmt/smtlib/parser/__init__.py
# to hide cython DeprecationWarning when importing module imp
#
# import warnings
# warnings.filterwarnings("ignore", category=DeprecationWarning)
import json
import logging
import time
import sys
from typing import Dict, List
import theorydd.formula as formula
from pysmt.fnode import FNode

from theorydd.solvers.solver import SMTEnumerator
from theorydd.solvers.mathsat_total import MathSATTotalEnumerator
from theorydd.solvers.mathsat_partial_extended import MathSATExtendedPartialEnumerator
from theorydd.solvers.mathsat_partial import MathSATPartialEnumerator
from theorydd.solvers.tabular import TabularPartialSMTSolver, TabularSMTSolver, TabularTotalSMTSolver
from theorydd.solvers.lemma_extractor import extract
from theorydd.constants import SAT, UNSAT

import src.kc.abstraction_decision_diagrams as add
import src.kc.theory_decision_diagrams as tdd
from src.kc.commands import Options, get_args

kc_logger = logging.getLogger("knowledge_compiler")

def print_models(models, boolean_mapping) -> None:
    """prints the models from allSMT computation on screen"""
    if boolean_mapping is not None:
        counter = 0
        for model in models:
            out = ""
            for elem in model:
                if elem.is_not():
                    out += "!"
                    elem = elem.args()[0]
                if elem in boolean_mapping.keys():
                    out += str(boolean_mapping[elem]) + ", "
                else:
                    out += str(elem) + ", "
            counter += 1
            print(counter, ": [", out[:len(out)-2], "]", sep="")
    else:
        print("\n".join(map(str, models)))

def get_phi(args: Options, data_logger: Dict) -> FNode:
    """load the input formula"""
    start_time = time.time()
    kc_logger.info("Loading phi...")
    if args.input is None:
        phi = formula.default_phi()
    else:
        phi = formula.read_phi(args.input)
    if args.negative:
        phi = formula.negate(phi)
    data_logger["phi size"] = formula.get_fnode_size(phi)
    kc_logger.info("Phi size: %s node(s)", str(data_logger["phi size"]))
    if args.preload_lemmas is not None:
        phi = formula.big_and([phi, formula.read_phi(args.preload_lemmas)])
    elapsed_time = time.time() - start_time
    data_logger["phi loading time"] = elapsed_time
    kc_logger.info("Loaded phi in %s seconds", str(elapsed_time))
    return phi


def do_pure_abstraction(phi: FNode, args: Options, data_logger: Dict) -> None:
    """DO ALL FUNCTIONS THAT DO NOT REQUIRE All-SMT to be computed"""
    # ABSTRACTION dDNNF
    if args.abstraction_dDNNF:
        add.abstr_ddnnf(phi, args, data_logger)
    # ABSTRACTION BDD
    if args.abstraction_bdd:
        add.abstr_bdd(phi, args, data_logger)
    # ABSTRACTION SDD
    if args.abstraction_sdd:
        add.abstr_sdd(phi, args, data_logger)
    # LDD
    if args.ldd:
        add.ldd(phi, args, data_logger)
    # XSDD
    if args.xsdd:
        add.xsdd(phi, args, data_logger)


def dump_details(data_logger: Dict, args: Options) -> None:
    """dump details on file"""
    filename = args.details_file
    with open(filename, 'w', encoding='utf8') as f:
        json.dump(data_logger, f)


def load_details(args: Options) -> Dict:
    """load details from file"""
    filename = args.load_details
    data_logger = {}
    with open(filename, 'r', encoding='utf8') as f:
        data_logger = json.load(f)
    return data_logger


def get_solver(args: Options) -> SMTEnumerator:
    """returns the solver chosen by the user"""
    if args.solver == "total":
        return MathSATTotalEnumerator()
    elif args.solver == "partial":
        return MathSATExtendedPartialEnumerator()
    elif args.solver == "extended_partial":
        return MathSATPartialEnumerator()
    elif args.solver == "tabular_total":
        return TabularTotalSMTSolver()
    elif args.solver == "tabular_partial":
        return TabularPartialSMTSolver()
    else:
        # default on total solver
        return MathSATTotalEnumerator()


def is_smt_phase_necessary(args: Options):
    """checks if it is necessary to compute the all-SMT phase"""
    return args.save_lemmas or args.tsdd or args.tbdd or args.print_lemmas or args.print_models or args.tdDNNF


def smt_phase(phi: FNode, args: Options, data_logger: Dict):
    """SMT phase"""
    smt_solver = get_solver(args)

    tlemmas: List[FNode] | None = None
    sat_result = None
    if args.load_lemmas is None:
        # COMPUTE LEMMAS IF NECESSARY
        sat_result, tlemmas, boolean_mapping = extract(
            phi,
            smt_solver,
            enumerate_true=args.enumerate_true,
            use_boolean_mapping=(not args.no_boolean_mapping),
            computation_logger=data_logger)

        if args.count_models:
            models_total = len(smt_solver.get_models())
            data_logger["All-SMT models"] = models_total
            kc_logger.info("All-SMT total models %s", str(models_total))

        if args.print_models:
            if isinstance(smt_solver, TabularSMTSolver):
                print("Models not available from Tabular computation")
            else:
                print("All-SMT models:")
                models = smt_solver.get_models()
                print_models(models, boolean_mapping)

        data_logger["total lemmas"] = len(tlemmas)
        kc_logger.info("All-SMT found %s theory lemmas", str(len(tlemmas)))

        # THIS IS ALWAYS PRINTED ON STDOUT WHEN THE OPTION IS ENABLED
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
    else:
        tlemmas = [formula.read_phi(args.load_lemmas)]

    # laod sat result from logger if available
    if "All-SMT result" in data_logger.keys():
        sat_result_string = data_logger["All-SMT result"]
        if sat_result_string == "SAT":
            sat_result = SAT
        else:
            sat_result = UNSAT

    # T-dDNNF
    if args.tdDNNF:
        tdd.theory_ddnnf(phi, args, data_logger, smt_solver, tlemmas, sat_result)

    # T-BDD
    if args.tbdd:
        tdd.theory_bdd(phi, args, data_logger, smt_solver, tlemmas, sat_result)

    # T-SDD
    if args.tsdd:
        tdd.theory_sdd(phi, args, data_logger, smt_solver, tlemmas, sat_result)

def _set_logging_handlers(args: Options) -> None:
    """set logging handlers"""
    logging_handlers = []
    if args.verbose:
        logging_handlers.append(logging.StreamHandler(sys.stdout))
    if args.log_file is not None:
        logging_handlers.append(logging.FileHandler(args.log_file, mode='w', encoding='utf8'))
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
        handlers=logging_handlers
    )

def main() -> None:
    '''Main function for this project'''
    global_start_time = time.time()
    args = get_args()

    _set_logging_handlers(args)

    kc_logger.info("Starting computation...")
    if args.load_details:
        data_logger = load_details(args)
        # in case of computation restarting, adjust start time accordingly
        if data_logger["total computation time"] is not None:
            global_start_time -= data_logger["total computation time"]
    else:
        data_logger = {}

    # LOAD FORMULA
    phi = get_phi(args, data_logger)

    # ONLY NEEDS ABSTRACTION
    do_pure_abstraction(phi, args, data_logger)

    # SMT PHASE (ONLY DONE IF NECESSARY)
    if is_smt_phase_necessary(args):
        smt_phase(phi, args, data_logger)

    global_elapsed_time = time.time() - global_start_time
    kc_logger.info("All done in %s seconds", str(global_elapsed_time))
    data_logger['total computation time'] = global_elapsed_time
    if args.details_file is not None:
        dump_details(data_logger, args)


if __name__ == "__main__":
    main()
