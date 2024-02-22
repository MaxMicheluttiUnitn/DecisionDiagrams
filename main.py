'''the main module for this project'''
import time
import logging
import sys
import json

# ADD these lines to .local/lib/python3.10/site-packages/pysmt/smtlib/parser/__init__.py
# to hide cython DeprecationWarning when importing module imp
#
# import warnings
# warnings.filterwarnings("ignore", category=DeprecationWarning)

import formula
import commands
from smt_solver import SAT, UNSAT, SMTSolver
import decision_diagrams


def get_phi(args, computation_logger):
    """gets the input formula to run this project"""
    start_time = time.time()
    print("Building Phi...")
    if args.input is None:
        phi = formula.get_phi()
    else:
        phi = formula.read_phi(args.input)
    elapsed_time = time.time()-start_time
    print("Formula built in ", elapsed_time, " seconds")
    computation_logger["phi building time"] = elapsed_time
    return phi


def normalize_phi_and_get_solver(phi, args, computation_logger):
    """computes normalization on phi"""
    # pylint: disable=unused-argument
    start_time = time.time()
    print("Normalizing phi according to solver...")
    smt_solver = SMTSolver()
    normal_phi = formula.get_normalized(phi, smt_solver.get_converter())
    elapsed_time = time.time()-start_time
    print("Phi was normalized in ", elapsed_time, " seconds")
    computation_logger["phi normalization time"] = elapsed_time
    return normal_phi, smt_solver


def all_sat_computation(phi, smt_solver, args, computation_logger):
    """computes all sat returns models and lemmas"""
    if args.pure_abstraction:
        # DD generation is the same for SAT and UNSTA in pure boolean world
        return SAT,[]
    start_time = time.time()
    print("Starting All Sat computation...")
    boolean_mapping = formula.get_boolean_mapping(phi)
    if smt_solver.check_all_sat(phi, boolean_mapping) == UNSAT:
        print("Computed All Sat in ", time.time()-start_time, " seconds")
        print("Phi is T-UNSAT. Cannot generate any DD...")
        return UNSAT, []
    elapsed_time = time.time()-start_time
    print("Computed All Sat in ", elapsed_time, " seconds")
    computation_logger["All-SAT computation time"] = elapsed_time
    print("Phi is T-SAT")
    models = smt_solver.get_models()
    if args.count_models:
        total_models = len(models)
        print("ALL-SAT Models: ", total_models)
        computation_logger["All-SAT models"] = total_models
    if args.print_models:
        print("Models:")
        if not boolean_mapping is None:
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
    lemmas = smt_solver.get_theory_lemmas()
    if args.print_lemmas:
        print("T-lemmas:")
        print("\n".join(map(lambda x: x.serialize(), lemmas)))
    computation_logger["T-lemmas amount"] = len(lemmas)
    return SAT,lemmas


def add_theory_lemmas(phi, lemmas, args, computation_logger):
    """computes the conjunction of phi with the lemmas"""
    if args.pure_abstraction:
        phi_and_lemmas = phi
    else:
        start_time = time.time()
        print("Adding theory lemmas to phi...")
        phi_and_lemmas = formula.get_phi_and_lemmas(phi, lemmas)
        elapsed_time = time.time()-start_time
        print("Theory lemmas added to phi in ",
              elapsed_time, " seconds")
        computation_logger["phi and theory lemmas computation time"] = elapsed_time
    return phi_and_lemmas


def find_qvars(phi, phi_and_lemmas, args, computation_logger):
    """finds the atoms on which to existentially quantify"""
    # pylint: disable=unused-argument
    if args.pure_abstraction:
        return []
    start_time = time.time()
    print("Finding fresh atoms from all-sat computation...")
    phi_atoms = formula.get_atoms(phi)
    phi_lemma_atoms = formula.get_atoms(phi_and_lemmas)
    new_theory_atoms = []
    if len(phi_atoms) < len(phi_lemma_atoms):
        new_theory_atoms = formula.atoms_difference(phi_atoms, phi_lemma_atoms)
        # quantified_phi = formula.existentially_quantify(
        #     phi_and_lemmas, new_theory_atoms)
    computation_logger["fresh T-atoms detected"] = len(new_theory_atoms)
    elapsed_time = time.time()-start_time
    print("Fresh atoms found in ",
          elapsed_time, " seconds")
    computation_logger["fresh T-atoms detection time"] = elapsed_time
    return new_theory_atoms


def process_sdd(phi_and_lemmas, qvars, args, computation_logger):
    """processes the SDD for phi_and_lemmas"""
    start_time = time.time()
    print("Starting SDD Procesing...")
    computation_logger["SDD"] = {}
    decision_diagrams.compute_sdd(phi_and_lemmas, output_file=args.sdd_output,
                                  vtree_type=args.vtree, vtree_output=args.vtree_output,
                                  print_mapping=args.print_mapping,
                                  dump_abstraction=args.dump_abstraction,
                                  count_models=args.count_models,
                                  count_nodes=args.count_nodes,
                                  qvars=qvars,
                                  computation_logger = computation_logger)
    elapsed_time = time.time()-start_time
    print("SDD processed in ", elapsed_time, " seconds")
    computation_logger["SDD"]["total processing time"] = elapsed_time


def process_bdd(phi_and_lemmas, qvars, args, computation_logger):
    """processes the BDD for phi_and_lemmas"""
    start_time = time.time()
    print("Starting BDD Procesing...")
    computation_logger["BDD"] = {}
    decision_diagrams.compute_bdd_cudd(phi_and_lemmas, output_file=args.bdd_output,
                                       print_mapping=args.print_mapping,
                                       dump_abstraction=args.dump_abstraction,
                                       count_models=args.count_models,
                                       count_nodes=args.count_nodes,
                                       qvars=qvars,
                                       computation_logger = computation_logger)
    elapsed_time = time.time()-start_time
    print("BDD processed in ", elapsed_time, " seconds")
    computation_logger["BDD"]["total processing time"] = elapsed_time


def process_xsdd(phi, args, computation_logger):
    """processes the XSDD for phi"""
    # pylint: disable=unused-argument
    logger = logging.getLogger("pywmi.engines.xsdd.engine")
    logger.setLevel(logging.DEBUG)
    start_time = time.time()
    print("Starting XSDD Procesing...")
    computation_logger["XSDD"] = {}
    decision_diagrams.compute_xsdd(phi,computation_logger = computation_logger)
    elapsed_time = time.time()-start_time
    print("XSDD processed in ", elapsed_time , " seconds")
    computation_logger["XSDD"]["total processing time"] = elapsed_time


def main() -> None:
    '''Main function for this project'''
    global_start_time = time.time()

    args = commands.get_args()
    computation_logger = {}
    # GETTING PHI
    phi = get_phi(args, computation_logger)

    # NORMALIZING PHI
    phi, smt_solver = normalize_phi_and_get_solver(phi, args, computation_logger)

    # COMPUTING ALL-SAT
    satisfiablity, lemmas = all_sat_computation(phi, smt_solver, args, computation_logger)

    if satisfiablity == SAT:
        computation_logger["all sat result"] = "SAT"

        # ADDING THEORY LEMMAS
        phi_and_lemmas = add_theory_lemmas(phi, lemmas, args, computation_logger)

        # FINDING ATOMS TO EXISTETIALLY QUANTIFY ON
        new_theory_atoms = find_qvars(phi, phi_and_lemmas, args, computation_logger)

        # GENERATING DDs
        if args.sdd:
            process_sdd(phi_and_lemmas, new_theory_atoms, args, computation_logger)
        if args.bdd:
            process_bdd(phi_and_lemmas, new_theory_atoms, args, computation_logger)
        if args.xsdd:
            process_xsdd(phi, args, computation_logger)
    else:
        computation_logger["all sat result"] = "UNSAT"

    elapsed_time = time.time()-global_start_time
    print("All done in ",elapsed_time, " seconds")
    computation_logger["total computation time"] = elapsed_time
    
    if args.details is not None:
        with open(args.details, 'w', encoding='utf8') as f:
            json.dump(computation_logger, f)


if __name__ == "__main__":
    main()
