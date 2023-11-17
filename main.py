'''the main module for this project'''

import time
import decision_diagrams
from smt_solver import UNSAT, SMTSolver, FNode
import commands
import formula
from typing import Set

from pysmt.shortcuts import And

import logging


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
    boolean_mapping = formula.get_boolean_mapping(phi)
    print("Phi was normalized in ", time.time()-start_time, " seconds")

    # COMPUTING ALL-SAT
    start_time = time.time()
    print("Starting All Sat computation")
    if smt_solver.check_all_sat(phi, boolean_mapping) == UNSAT:
        print("Computed All Sat in ", time.time()-start_time, " seconds")
        print("Phi is UNSAT. Cannot generate any DD...")
        return
    print("Computed All Sat in ", time.time()-start_time, " seconds")
    print("Phi is SAT")
    models = smt_solver.get_models()
    if args.print_models:
        print(len(models), " models:")
        print("\n".join(map(str, models)))
    lemmas = smt_solver.get_theory_lemmas()
    if args.print_lemmas:
        print("T-lemmas:")
        print("\n".join(map(lambda x: x.serialize(), lemmas)))

    # print(models[24])
    # phi_ans_model = And(phi, *models[24])
    # if smt_solver.check_all_sat(phi_ans_model) == UNSAT:
    #     print("un satisfiable")
    # else:
    #     print("sat")

    atoms = formula.get_atoms(phi)
    print(atoms)

    lemmas_atom_set : Set[FNode] = set()
    for lemma in lemmas:
        lemma_atoms=formula.get_atoms(lemma)
        for latom in lemma_atoms:
            lemmas_atom_set.add(latom)
    print(list(lemmas_atom_set))

    # ADDING THEORY LEMMAS
    if args.pure_abstraction:
        phi_and_lemmas = phi
    else:
        start_time = time.time()
        print("Adding theory lemmas to phi...")
        phi_and_lemmas = formula.get_phi_and_lemmas(phi, lemmas)
        print("Theory lemmas added to phi in ",
              time.time()-start_time, " seconds")

    # GENERATING DDs
    if args.sdd:
        start_time = time.time()
        print("Starting SDD Procesing...")
        decision_diagrams.compute_sdd(phi_and_lemmas, output_file=args.sdd_output,
                                      vtree_type=args.vtree, vtree_output=args.vtree_output,
                                      print_mapping=args.print_mapping, dump_abstraction=args.dump_abstraction,
                                      count_models=args.count_models, all_sat_models=models)
        print("SDD processed in ", time.time()-start_time, " seconds")
    if args.bdd:
        start_time = time.time()
        print("Starting BDD Procesing...")
        decision_diagrams.compute_bdd_cudd(phi_and_lemmas, output_file=args.bdd_output,
                                           print_mapping=args.print_mapping, dump_abstraction=args.dump_abstraction,
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
