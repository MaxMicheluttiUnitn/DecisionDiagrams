"""main module to query dDNNF formulas"""

import json
from theorydd.formula import load_abstraction_function

from src.query.tsdd.commands import get_args
from src.query.util import is_tsdd_loading_folder_correct
from src.query.tsdd.manager import TSDDQueryManager

def main():
    """main function to query T-BDD formulas"""
    args = get_args()

    if not is_tsdd_loading_folder_correct(args.load_tsdd):
        raise ValueError("The folder where the T-BDD files are stored was not found, or some files are missing from it.")

    # LOAD REFINEMENT
    abstraction_mapping = load_abstraction_function(args.load_tbdd + "/abstraction.json")
    refinement_mapping = {v: k for k, v in abstraction_mapping.items()}

    # LOAD QVARS
    with open(args.load_tbdd + "/qvars.qvars", "r", encoding='utf8') as qvars_file:
        qvars = json.load(qvars_file)
    
    # FILTER REFINEMENT BY REMOVING KEYS IN QVARS
    keys_to_remove = set()
    for key in refinement_mapping.keys():
        if key in qvars:
            keys_to_remove.add(key)
    for key in keys_to_remove:
        del refinement_mapping[key]
    
    query_manager = TSDDQueryManager(args.load_tsdd, refinement_mapping)

    if args.consistency:
        query_manager.check_consistency()

    if args.validity:
        query_manager.check_validity()

    if args.entail_clause is not None:
        query_manager.check_entail_clause(args.entail_clause)

    if args.implicant is not None:
        query_manager.check_implicant(args.implicant)

    if args.count:
        query_manager.count_models()

    if args.enumerate:
        query_manager.enumerate_models()

    if args.condition is not None:
        query_manager.condition(args.condition, args.save_conditioned)


if __name__ == "__main__":
    main()
