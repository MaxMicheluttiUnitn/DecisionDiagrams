from typing import List

VALID_VTREE = ["left","right","balanced","vertical","random"]

def parse_args(args:List[str]) -> dict:
    options = {
        "sdd": False,
        "bdd": False,
        "vtree": None,
        "input": None,
        "sdd-out": None,
        "bdd-out": None,
        "print-models": False,
        "print-lemmas": False
    }
    for arg in args:
        if arg == "--sdd":
            options["sdd"] = True
            continue
        if arg == "--bdd":
            options["bdd"] = True
            continue
        if arg == "--print-models":
            options["print-models"] = True
            continue
        if arg == "--print-lemmas":
            options["print-lemmas"] = True
            continue
        if arg.startswith("--vtree="):
            split_arg = arg.split("=")
            if len(split_arg) == 2 and split_arg[1] in VALID_VTREE:
                options["vtree"] = split_arg[1]
            continue
        if arg.startswith("--input="):
            split_arg = arg.split("=")
            if len(split_arg) == 2:
                options["input"] = split_arg[1]
            continue
        if arg.startswith("--sdd-output="):
            split_arg = arg.split("=")
            if len(split_arg) == 2:
                options["sdd-out"] = split_arg[1]
            continue
        if arg.startswith("--bdd-output="):
            split_arg = arg.split("=")
            if len(split_arg) == 2:
                options["bdd-out"] = split_arg[1]
            continue
        if arg == "--help" or arg == "-h":
            help()
            continue
    return options

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