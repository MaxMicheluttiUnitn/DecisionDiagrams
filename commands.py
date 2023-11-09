import argparse

VALID_VTREE = ["left", "right", "balanced", "vertical", "random"]


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
        "--print_models",
        help="Print the models obtained from All-SAT computation",
        action="store_true")
    parser.add_argument(
        "--print_lemmas",
        help="Print the lemmas generated during the All-SAT compiutation",
        action="store_true")
    parser.add_argument(
        "--vtree",
        help="Specify V-Tree kind for SDD generation (default is right). Available values: "+str(
            VALID_VTREE),
        type=str,
        choices=VALID_VTREE)
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
        help="Specify a .dot or .svg file to output the SDD (default is sdd.dot)",
        type=str)
    parser.add_argument(
        "--bdd_output",
        help="Specify a .svg file to output the BDD (default is bdd.svg)",
        type=str)
    parser.add_argument(
        "--pure_abstraction",
        help="Use only the boolean abstraction (without lemmas) for the DD generation",
        action="store_true")
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
