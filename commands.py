"""module to handle the options for the main process"""
import argparse

VALID_VTREE = ["left", "right", "balanced", "vertical", "random"]

VALID_LDD_THEORY = ["TVPI","TVPIZ","UTVPIZ","BOX","BOXZ"]

VALID_SOLVER = ["partial","total"]

def get_args() -> argparse.Namespace:
    ' ' 'Reads the args from the command line' ' '
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--sdd",
        help="Generate the SDD of the formula",
        action="store_true")
    parser.add_argument(
        "--xsdd",
        help="Generate the XSDD of the formula",
        action="store_true")
    parser.add_argument(
        "--bdd",
        help="Generate the BDD of the formula",
        action="store_true")
    parser.add_argument(
        "--ldd",
        help="Generate the LDD of the formula",
        action="store_true")
    parser.add_argument(
        "--print_models",
        help="Print the models obtained from All-SMT computation",
        action="store_true")
    parser.add_argument(
        "--print_lemmas",
        help="Print the lemmas generated during the All-SMT compiutation",
        action="store_true")
    parser.add_argument(
        "--vtree",
        help="Specify V-Tree kind for SDD generation (default is right). Available values: "+str(
            VALID_VTREE),
        type=str,
        choices=VALID_VTREE,
        default="right")
    parser.add_argument(
        "--ldd_theory",
        help="Specify the theory to use with LDDs. Available values: "+str(
            VALID_LDD_THEORY),
        type=str,
        choices=VALID_LDD_THEORY,
        default="TVPI")
    parser.add_argument(
        "--solver",
        help="Specify the solver you want to use to perform All-SMT. Available values: "+str(
            VALID_SOLVER),
        type=str,
        choices=VALID_SOLVER,
        default="partial")
    parser.add_argument(
        "--vtree_output",
        help="Specify a .dot or .svg file to save the vtree (by default the vtree is not saved)",
        type=str)
    parser.add_argument(
        "-i", "--input",
        help="Specify a file from witch to read the formula",
        type=str)
    parser.add_argument(
        "--sdd_output",
        help="Specify a .dot or .svg file to output the SDD",
        type=str)
    parser.add_argument(
        "--bdd_output",
        help="Specify a .dot or .svg file to output the BDD",
        type=str)
    parser.add_argument(
        "--ldd_output",
        help="Specify a .dot or .svg file to output the LDD",
        type=str)
    parser.add_argument(
        "-d", "--details",
        help="Specify a .json file to save the computation details",
        type=str)
    parser.add_argument(
        "--pure_abstraction",
        help="Use only the boolean abstraction (without lemmas) for the DD generation",
        action="store_true")
    parser.add_argument(
        "--no_boolean_mapping",
        help="Do not use a boolean mapping to enumerate when computing All SMT",
        action="store_true")
    parser.add_argument(
        "--dump_abstraction",
        help="Dump the boolean abstraction of the SMT formula instead of the actual formula",
        action="store_true")
    parser.add_argument(
        "--print_mapping",
        help="Print the boolean abstraction-SMT atom mapping",
        action="store_true")
    parser.add_argument(
        "--count_models",
        help="Print the amount of models represented by the DD",
        action="store_true")
    parser.add_argument(
        "--count_nodes",
        help="Print the amount of nodes in the generated DDs",
        action="store_true")
    parser.add_argument(
        "--count_vertices",
        help="Print the amount of vertices in the generated DDs",
        action="store_true")
    parser.add_argument(
        "--save_lemmas",
        help="Specify a .smt file to save the lemmas obtained from All-SMT",
        type=str)
    parser.add_argument(
        "--load_lemmas",
        help="Specify a .smt file to load lemmas from instead of performing All-SMT",
        type=str)
    # parser.add_argument(
    #     "--check_eq",
    #     help="Check the T-equivalence of the T-agnostic DD with the T-formula phi",
    #     action="store_true")
    args = parser.parse_args()
    return args


# def help() -> None:
#    ' ' 'Prints the help screen' ' '
#    print("Usage: python3 main.py [options]")
#    print("Available options:")
#    print("--help:              Print this list")
#    print("--sdd:               Generate the SDD of the formula")
#    print("--bdd:               Generate the BDD of the formula")
#    print("--vtree=[value]:     Specify V-Tree kind for SDD generation (default is right). Available values: ",VALID_VTREE)
#    print("--input=[file]:      Specify a file from witch to read the formula")
#    print("--sdd-output=[file]: Specify a .dot file to output the SDD (default is sdd.dot)")
#    print("--bdd-output=[file]: Specify a .svg file to output the BDD (default is bdd.svg)")
#    print("--print-models:      Print the models obtained from All-SAT computation")
#    print("--print-lemmas:      Print the lemmas generated during the All-SAT compiutation")
