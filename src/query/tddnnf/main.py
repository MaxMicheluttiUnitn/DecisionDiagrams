"""main module to query dDNNF formulas

This module expects that the D4 compiler was used for dDNNF compilation."""

import json
from theorydd.formula import load_refinement

from src.query.tddnnf.commands import get_args
from src.query.util import is_d4_tddnnf_loading_folder_correct
from src.query.tddnnf.manager import DDNNFQueryManager

def main():
    """main function to query T-dDNNF formulas"""
    args = get_args()

    if not is_d4_tddnnf_loading_folder_correct(args.load_tddnnf):
        raise ValueError("The folder where the T-dDNNF files are stored was not found, or some files are missing from it.")
    
    # load the important labels
    with open(args.load_tddnnf + "/mapping/import_labels.json", "r", encoding='utf8') as file:
        important_labels = json.load(file)

    # load refinement funvtion as a mapping
    refinement_mapping = load_refinement(
        args.load_tddnnf + "/mapping/mapping.json")
    
    # remove non important items from the mapping
    keys_to_remove = set()
    for key in refinement_mapping.keys():
        if key not in important_labels:
            keys_to_remove.add(key)
    for key in keys_to_remove:
        del refinement_mapping[key]
    
    query_manager = DDNNFQueryManager(args.load_tddnnf, refinement_mapping)

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
