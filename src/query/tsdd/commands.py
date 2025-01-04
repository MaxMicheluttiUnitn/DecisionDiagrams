"""module to handle the options for the main T-SDD quering tool"""
import argparse
from dataclasses import dataclass

@dataclass
class TSDDQueryOptions:
    """dataclass that holds options for the tool"""
    load_tsdd: str
    consistency: bool
    validity: bool
    entail_clause: str | None
    implicant: str | None
    count: bool
    enumerate: bool
    condition: str | None
    save_conditioned: str | None

    def __init__(self, args: argparse.Namespace):
        self.load_tbdd = args.load_tsdd
        # trim the trailing slash if it exists
        if self.load_tsdd.endswith("/"):
            self.load_tsdd = self.load_tsdd[:-1]
        self.consistency = args.consistency
        self.validity = args.validity
        self.entail_clause = args.entail_clause
        self.implicant = args.implicant
        self.count = args.count
        self.enumerate = args.enumerate
        self.condition = args.condition
        self.save_conditioned = args.save_conditioned

def get_args() -> TSDDQueryOptions:
    """Reads the args from the command line"""
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--load_tsdd",
        help="Specify the path to the folder where all necessary T-SDD files are stored",
        type=str,
        required=True)
    parser.add_argument(
        "--consistency",
        help="Query the T-SDD to check if the encoded formula is consistent",
        action="store_true")
    parser.add_argument(
        "--validity",
        help="Query the T-SDD to check if the encoded formula is valid",
        action="store_true")
    parser.add_argument(
        "--entail_clause",
        help="Query the T-SDD to check if the encoded formula entails the clause from the specified smt2 file",
        type=str)
    parser.add_argument(
        "--implicant",
        help="Query the T-SDD to check if the term in the specified smt2 file is an implicant for the encoded formula",
        type=str)
    parser.add_argument(
        "--count",
        help="Query the T-SDD to count the number of models for the encoded formula",
        action="store_true")
    parser.add_argument(
        "--enumerate",
        help="Query the T-SDD to enumerate all models for the encoded formula",
        action="store_true")
    parser.add_argument(
        "--condition",
        help="Transform the T-SDD in T-SDD | alpha, where alpha is a literal or a cube specified in the provided .smt2 file",
        type=str)
    parser.add_argument(
        "--save_conditioned",
        help="Specify the path to the .smt2 file where the conditioned T-SDD will be saved",
        type=str)
    args = parser.parse_args()
    return TSDDQueryOptions(args)
