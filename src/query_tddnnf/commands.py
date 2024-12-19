"""module to handle the options for the main T-dDNNF quering tool"""
import argparse
from dataclasses import dataclass


@dataclass
class TDDNNFQueryOptions:
    """dataclass that holds options for the tool"""
    load_tddnnf: str
    consistency: bool
    validity: bool
    entail_clause: str | None
    implicant: str | None
    count: bool
    enumerate: bool
    condition: str | None
    save_conditioned: str | None

    def __init__(self, args: argparse.Namespace):
        self.load_tddnnf = args.load_tddnnf
        self.consistency = args.consistency
        self.validity = args.validity
        self.entail_clause = args.entail_clause
        self.implicant = args.implicant
        self.count = args.count
        self.enumerate = args.enumerate
        self.condition = args.condition
        self.save_conditioned = args.save_conditioned

def get_args() -> TDDNNFQueryOptions:
    """Reads the args from the command line"""
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--load_tddnnf",
        help="Specify the path to the folder where all necessary T-dDNNF files are stored",
        type=str,
        required=True)
    parser.add_argument(
        "--consistency",
        help="Query the T-dDNNF to check if the encoded formula is consistent",
        action="store_true")
    parser.add_argument(
        "--validity",
        help="Query the T-dDNNF to check if the encoded formula is valid",
        action="store_true")
    parser.add_argument(
        "--entail_clause",
        help="Query the T-dDNNF to check if the encoded formula entails the clause from the specified smt2 file",
        type=str)
    parser.add_argument(
        "--implicant",
        help="Query the T-dDNNF to check if the term in the specified smt2 file is an implicant for the encoded formula",
        type=str)
    parser.add_argument(
        "--count",
        help="Query the T-dDNNF to count the number of models for the encoded formula",
        action="store_true")
    parser.add_argument(
        "--enumerate",
        help="Query the T-dDNNF to enumerate all models for the encoded formula",
        action="store_true")
    parser.add_argument(
        "--condition",
        help="Transform the T-dDNNF in T-dDNNF | alpha, where alpha is a literal or a conjuction of literals specified in the provided .smt2 file",
        type=str)
    parser.add_argument(
        "--save_conditioned",
        help="Specify the path to the .smt2 file where the conditioned T-dDNNF will be saved",
        type=str)
    args = parser.parse_args()
    return TDDNNFQueryOptions(args)
