from theorydd.lemma_extractor import find_qvars
import theorydd.formula as formula
from theorydd.smt_solver_partial import PartialSMTSolver

def main():
    input_file = "benchmarks/randgen/data/problems_b10_r10_d4_m25_s1234/01/b10_d4_r10_s1234_01.smt2"
    lemma_file = "benchmarks/randgen/tmp/problems_b10_r10_d4_m25_s1234/01/b10_d4_r10_s1234_01.smt2"
    phi = formula.read_phi(input_file)
    tlemmas = formula.read_phi(lemma_file)

    solver = PartialSMTSolver()

    phi = formula.get_normalized(phi, solver.get_converter())
    tlemmas = formula.get_normalized(tlemmas, solver.get_converter())

    phi_and_lemmas = formula.get_phi_and_lemmas(phi,[tlemmas])

    qvars = find_qvars(phi,phi_and_lemmas,{},False)

    print("ORIG. VARS")
    atoms = formula.get_atoms(phi)
    for a in atoms:
        print(a)

    print("QVARS:")
    for v in qvars:
        print(v)

if __name__ == "__main__":
    main()