import time
import decision_diagrams
from smt_solver import UNSAT,SMTSolver
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
    print("Formula built in ",time.time()-start_time," seconds")
    start_time = time.time()
    print("Starting All Sat computation")
    smt_solver = SMTSolver()
    if smt_solver.check_all_sat(phi) == UNSAT:
        print("Computed All Sat in ",time.time()-start_time," seconds")
        print("Phi is UNSAT")
        return
    print("Computed All Sat in ",time.time()-start_time," seconds")
    print("Phi is SAT")
    if args.print_models:
        print("Models:")
        print("\n".join(map(str, smt_solver.get_models())))
    if args.print_lemmas:
        print("T-lemmas:")
        print("\n".join(map(lambda x: x.serialize(), smt_solver.get_theory_lemmas())))
    if args.sdd:
        start_time = time.time()
        print("Starting SDD Procesing...")
        decision_diagrams.compute_sdd(phi,output_file=args.sdd_output,vtree_type=args.vtree)
        print("SDD processed in ",time.time()-start_time," seconds")
    if args.bdd:
        start_time = time.time()
        print("Starting BDD Procesing...")
        decision_diagrams.compute_bdd(phi,output_file=args.bdd_output)
        print("BDD processed in ",time.time()-start_time," seconds")


if __name__ == "__main__":
    main()
