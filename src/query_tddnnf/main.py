"""main module to query dDNNF formulas"""

from src.query_tddnnf.commands import get_args
from src.query_tddnnf.util import is_tddnnf_loading_folder_correct
from src.query_tddnnf.queries import check_consistency, check_validity, check_entail_clause, check_implicant, count_models, enumerate_models, condition_tddnnf


def main():
    """main function to query dDNNF formulas"""
    args = get_args()

    if not is_tddnnf_loading_folder_correct(args.load_tddnnf):
        print("The folder where the dDNNF files are stored was not found, or some files are missing from it.")
        return

    if args.consistency:
        check_consistency(args.load_tddnnf)

    if args.validity:
        check_validity(args.load_tddnnf)

    if args.entail_clause is not None:
        check_entail_clause(args.load_tddnnf, args.entail_clause)

    if args.implicant is not None:
        check_implicant(args.load_tddnnf, args.implicant)

    if args.count:
        count_models(args.load_tddnnf)

    if args.enumerate:
        enumerate_models(args.load_tddnnf)

    if args.condition is not None:
        condition_tddnnf(args.load_tddnnf, args.condition,
                         args.save_conditioned)


if __name__ == "__main__":
    main()
