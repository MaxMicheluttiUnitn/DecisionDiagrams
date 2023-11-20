'''the main module for this project'''
import logging
import time
import decision_diagrams
from smt_solver import UNSAT, SMTSolver
import commands
import formula


def main() -> None:
    '''Main function for this project'''
    args = commands.get_args()
    start_time = time.time()
    print("Building Phi...")
    if args.input is None:
        phi = formula.get_phi()
    else:
        phi = formula.read_phi(args.input)
    print("Formula built in ", time.time()-start_time, " seconds")

    # NORMALIZING PHI
    start_time = time.time()
    print("Normalizing phi according to solver...")
    smt_solver = SMTSolver()
    phi = formula.get_normalized(phi, smt_solver.get_converter())
    print("Phi was normalized in ", time.time()-start_time, " seconds")

    # COMPUTING ALL-SAT
    start_time = time.time()
    print("Starting All Sat computation...")
    boolean_mapping = formula.get_boolean_mapping(phi)
    if smt_solver.check_all_sat(phi, boolean_mapping) == UNSAT:
        print("Computed All Sat in ", time.time()-start_time, " seconds")
        print("Phi is UNSAT. Cannot generate any DD...")
        return
    print("Computed All Sat in ", time.time()-start_time, " seconds")
    print("Phi is SAT")
    models = smt_solver.get_models()
    if args.print_models:
        print(len(models), " models:")
        counter = 0
        for model in models:
            out = ""
            for elem in model:
                if elem.is_not():
                    out += str(boolean_mapping[elem.args()[0]]) + ", "
                else:
                    out += str(boolean_mapping[elem]) + ", "
            counter+=1
            print(counter,": [",out[:len(out)-2],"]",sep="")
    lemmas = smt_solver.get_theory_lemmas()
    if args.print_lemmas:
        print("T-lemmas:")
        print("\n".join(map(lambda x: x.serialize(), lemmas)))

    # ADDING THEORY LEMMAS
    if args.pure_abstraction:
        phi_and_lemmas = phi
    else:
        start_time = time.time()
        print("Adding theory lemmas to phi...")
        phi_and_lemmas = formula.get_phi_and_lemmas(phi, lemmas)
        print("Theory lemmas added to phi in ",
              time.time()-start_time, " seconds")


    # NORMALIZING PHI AND LEMMAS
    # start_time = time.time()
    # print("Normalizing phi & lemmas according to solver...")
    # smt_solver = SMTSolver()
    # phi = formula.get_normalized(phi, smt_solver.get_converter())
    # print("Phi & lemmas was normalized in ", time.time()-start_time, " seconds")
    # print(formula.get_atoms(phi))
    # print(formula.get_atoms(phi_and_lemmas))

    # GENERATING DDs
    if args.sdd:
        start_time = time.time()
        print("Starting SDD Procesing...")
        decision_diagrams.compute_sdd(phi_and_lemmas, output_file=args.sdd_output,
                                      vtree_type=args.vtree, vtree_output=args.vtree_output,
                                      print_mapping=args.print_mapping,
                                      dump_abstraction=args.dump_abstraction,
                                      count_models=args.count_models, all_sat_models=models)
        print("SDD processed in ", time.time()-start_time, " seconds")
    if args.bdd:
        start_time = time.time()
        print("Starting BDD Procesing...")
        decision_diagrams.compute_bdd_cudd(phi_and_lemmas, output_file=args.bdd_output,
                                           print_mapping=args.print_mapping,
                                           dump_abstraction=args.dump_abstraction,
                                           count_models=args.count_models)
        print("BDD processed in ", time.time()-start_time, " seconds")
    if args.xsdd:
        logger = logging.getLogger("pywmi.engines.xsdd.engine")
        logger.setLevel(logging.DEBUG)
        start_time = time.time()
        print("Starting XSDD Procesing...")
        decision_diagrams.compute_xsdd(phi)
        print("XSDD processed in ", time.time()-start_time, " seconds")


if __name__ == "__main__":
    main()
