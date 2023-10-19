from typing import List
import argparse

VALID_VTREE = ["left","right","balanced","vertical","random"]

def get_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sdd", help="Generate the SDD of the formula",action="store_true")
    parser.add_argument("--bdd", help="Generate the BDD of the formula",action="store_true")
    parser.add_argument("--print_models", help="Print the models obtained from All-SAT computation",action="store_true")
    parser.add_argument("--print_lemmas", help="Print the lemmas generated during the All-SAT compiutation",action="store_true")
    parser.add_argument("--vtree", help="Specify V-Tree kind for SDD generation (default is right). Available values: "+str(VALID_VTREE),type=str)
    parser.add_argument("-i","--input", help="Specify a file from witch to read the formula",type=str)
    parser.add_argument("--sdd_output", help="Specify a .dot file to output the SDD (default is sdd.dot)",type=str)
    parser.add_argument("--bdd_output", help="Specify a .svg file to output the BDD (default is bdd.svg)",type=str)
    args = parser.parse_args()
    if not (args.vtree is None) and not (args.vtree in VALID_VTREE):
        args.vtree = None
    return args

def help():
    print("Usage: python3 main.py [options]")
    print("Available options:")
    print("--help:              Print this list")
    print("--sdd:               Generate the SDD of the formula")
    print("--bdd:               Generate the BDD of the formula")
    print("--vtree=[value]:     Specify V-Tree kind for SDD generation (default is right). Available values: ",VALID_VTREE)
    print("--input=[file]:      Specify a file from witch to read the formula")
    print("--sdd-output=[file]: Specify a .dot file to output the SDD (default is sdd.dot)")
    print("--bdd-output=[file]: Specify a .svg file to output the BDD (default is bdd.svg)")
    print("--print-models:      Print the models obtained from All-SAT computation")
    print("--print-lemmas:      Print the lemmas generated during the All-SAT compiutation")