'''the main module for this project'''
import sys
import logging
import time
import decision_diagrams
from smt_solver import UNSAT, SMTSolver
import commands
import formula


def get_phi(args):
    """gets the input formula to run this project"""
    start_time = time.time()
    print("Building Phi...")
    if args.input is None:
        phi = formula.get_phi()
    else:
        phi = formula.read_phi(args.input)
    print("Formula built in ", time.time()-start_time, " seconds")
    return phi


def normalize_phi_and_get_solver(phi, args):
    """computes normalization on phi"""

    start_time = time.time()
    print("Normalizing phi according to solver...")
    smt_solver = SMTSolver()
    normal_phi = formula.get_normalized(phi, smt_solver.get_converter())
    print("Phi was normalized in ", time.time()-start_time, " seconds")
    return normal_phi, smt_solver


def all_sat_computation(phi, smt_solver, args):
    """computes all sat returns models and lemmas"""
    start_time = time.time()
    print("Starting All Sat computation...")
    boolean_mapping = formula.get_boolean_mapping(phi)
    if smt_solver.check_all_sat(phi, boolean_mapping) == UNSAT:
        print("Computed All Sat in ", time.time()-start_time, " seconds")
        print("Phi is T-UNSAT. Cannot generate any DD...")
        sys.exit(0)
    print("Computed All Sat in ", time.time()-start_time, " seconds")
    print("Phi is T-SAT")
    models = smt_solver.get_models()
    if args.count_models:
        print("ALL-SAT Models: ", len(models))
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
    return models, lemmas


def add_theory_lemmas(phi, lemmas, args):
    """computes the conjunction of phi with the lemmas"""
    if args.pure_abstraction:
        phi_and_lemmas = phi
    else:
        start_time = time.time()
        print("Adding theory lemmas to phi...")
        phi_and_lemmas = formula.get_phi_and_lemmas(phi, lemmas)
        print("Theory lemmas added to phi in ",
              time.time()-start_time, " seconds")
    return phi_and_lemmas


def find_qvars(phi, phi_and_lemmas, args):
    """finds the atoms on which to existentially quantify"""
    start_time = time.time()
    print("Existentially quantifying new atoms generated in T-lemmas...")
    phi_atoms = formula.get_atoms(phi)
    phi_lemma_atoms = formula.get_atoms(phi_and_lemmas)
    new_theory_atoms = []
    if len(phi_atoms) < len(phi_lemma_atoms):
        new_theory_atoms = formula.atoms_difference(phi_atoms, phi_lemma_atoms)
        # quantified_phi = formula.existentially_quantify(
        #     phi_and_lemmas, new_theory_atoms)
    print("Theory lemmas existentially quantified in ",
          time.time()-start_time, " seconds")
    return new_theory_atoms

def processSDD(phi_and_lemmas,qvars,models,args):
    """processes the SDD for phi_and_lemmas"""
    start_time = time.time()
    print("Starting SDD Procesing...")
    decision_diagrams.compute_sdd(phi_and_lemmas, output_file=args.sdd_output,
                                    vtree_type=args.vtree, vtree_output=args.vtree_output,
                                    print_mapping=args.print_mapping,
                                    dump_abstraction=args.dump_abstraction,
                                    count_models=args.count_models, all_sat_models=models)
    print("SDD processed in ", time.time()-start_time, " seconds")

def processBDD(phi_and_lemmas,qvars,models,args):
    """processes the BDD for phi_and_lemmas"""
    start_time = time.time()
    print("Starting BDD Procesing...")
    decision_diagrams.compute_bdd_cudd(phi_and_lemmas, output_file=args.bdd_output,
                                        print_mapping=args.print_mapping,
                                        dump_abstraction=args.dump_abstraction,
                                        count_models=args.count_models,
                                        qvars=qvars)
    print("BDD processed in ", time.time()-start_time, " seconds")

def processXSDD(phi,args):
    """processes the XSDD for phi"""
    logger = logging.getLogger("pywmi.engines.xsdd.engine")
    logger.setLevel(logging.DEBUG)
    start_time = time.time()
    print("Starting XSDD Procesing...")
    decision_diagrams.compute_xsdd(phi)
    print("XSDD processed in ", time.time()-start_time, " seconds")

def main() -> None:
    '''Main function for this project'''
    args = commands.get_args()
    # GETTING PHI
    phi = get_phi(args)

    # NORMALIZING PHI
    phi, smt_solver = normalize_phi_and_get_solver(phi, args)

    # COMPUTING ALL-SAT
    models, lemmas = all_sat_computation(phi, smt_solver, args)

    # ADDING THEORY LEMMAS
    phi_and_lemmas = add_theory_lemmas(phi, lemmas, args)

    # FINDING ATOMS TO EXISTETIALLY QUANTIFY ON
    new_theory_atoms = find_qvars(phi, phi_and_lemmas, args)

    # GENERATING DDs
    if args.sdd:
        processSDD(phi_and_lemmas,new_theory_atoms,models,args)
    if args.bdd:
        processBDD(phi_and_lemmas,new_theory_atoms,models,args)
    if args.xsdd:
        processXSDD(phi,args)


if __name__ == "__main__":
    main()
