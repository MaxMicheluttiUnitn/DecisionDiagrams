"""main module to query dDNNF formulas"""

from theorydd.formula import load_refinement
from theorydd.smt_solver import SMTSolver

from src.query_tddnnf.commands import get_args
from src.util import is_tddnnf_loading_folder_correct, normalize_mapping
from src.query_tddnnf.queries import check_consistency, check_validity, check_entail_clause, check_implicant, count_models, enumerate_models, condition_tddnnf


def main():
    """main function to query dDNNF formulas"""
    args = get_args()

    if not is_tddnnf_loading_folder_correct(args.load_tddnnf):
        print("The folder where the dDNNF files are stored was not found, or some files are missing from it.")
        return

    normalizer_solver = SMTSolver()

    refinement_mapping = load_refinement(
        args.load_tddnnf + "/mapping/mapping.json")

    refinement_mapping = normalize_mapping(
        refinement_mapping, normalizer_solver)
    
    abstraction_mapping = {v: k for k, v in refinement_mapping.items()}

    if args.consistency:
        check_consistency(args.load_tddnnf)

    if args.validity:
        check_validity(args.load_tddnnf)

    if args.entail_clause is not None:
        check_entail_clause(args.load_tddnnf,
                            refinement_mapping,
                            abstraction_mapping,
                            normalizer_solver,
                            args.entail_clause)

    if args.implicant is not None:
        check_implicant(args.load_tddnnf,
                        refinement_mapping,
                        abstraction_mapping,
                        normalizer_solver,
                        args.implicant)

    if args.count:
        count_models(args.load_tddnnf)

    if args.enumerate:
        enumerate_models(args.load_tddnnf, refinement_mapping)

    if args.condition is not None:
        condition_tddnnf(args.load_tddnnf,
                         refinement_mapping,
                         abstraction_mapping,
                         normalizer_solver,
                         args.condition,
                         args.save_conditioned)


if __name__ == "__main__":
    main()
