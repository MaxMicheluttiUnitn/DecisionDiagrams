"""module to handle the options for the main process"""
import argparse
from dataclasses import dataclass

VALID_VTREE = ["left", "right", "balanced", "vertical", "random"]

VALID_LDD_THEORY = ["TVPI", "TVPIZ", "UTVPIZ", "BOX", "BOXZ"]

VALID_SOLVER = ["partial", "total", "full_partial",
                "tabular_total", "tabular_partial"]

VALID_DDNNF_COMPILER = ["c2d", "d4"]


@dataclass
class Options:
    """dataclass that holds options for the tool"""
    tsdd: bool
    xsdd: bool
    tbdd: bool
    ldd: bool
    print_models: bool
    print_lemmas: bool
    tvtree: str
    abstraction_vtree: str
    ldd_theory: str
    solver: str
    tvtree_output: str | None
    abstraction_vtree_output: str | None
    input: str | None
    tsdd_output: str | None
    tbdd_output: str | None
    abstraction_sdd_output: str | None
    abstraction_bdd_output: str | None
    ldd_output: str | None
    details_file: str | None
    load_details: str | None
    abstraction_bdd: bool
    abstraction_sdd: bool
    no_boolean_mapping: bool
    dump_abstraction: bool
    print_mapping: bool
    count_models: bool
    count_nodes: bool
    count_vertices: bool
    save_lemmas: str | None
    load_lemmas: str | None
    verbose: bool
    abstraction_dDNNF: bool
    tdDNNF: bool
    abstraction_dDNNF_output: str | None
    tdDNNF_output: str | None
    keep_c2d_temp: bool
    no_dDNNF_to_pysmt: bool
    dDNNF_compiler: str
    save_tbdd: str | None
    save_abstraction_bdd: str | None
    save_tsdd: str | None
    save_abstraction_sdd: str | None

    def __init__(self, args: argparse.Namespace):
        self.tsdd = args.tsdd
        self.xsdd = args.xsdd
        self.tbdd = args.tbdd
        self.ldd = args.ldd
        self.print_models = args.print_models
        self.print_lemmas = args.print_lemmas
        self.tvtree = args.tvtree
        self.abstraction_vtree = args.abstraction_vtree
        self.ldd_theory = args.ldd_theory
        self.solver = args.solver
        self.tvtree_output = args.tvtree_output
        self.abstraction_vtree_output = args.abstraction_vtree_output
        self.input = args.input
        self.tbdd_output = args.tbdd_output
        self.tsdd_output = args.tsdd_output
        self.abstraction_bdd_output = args.abstraction_bdd_output
        self.abstraction_sdd_output = args.abstraction_sdd_output
        self.ldd_output = args.ldd_output
        self.details_file = args.details_file
        self.abstraction_bdd = args.abstraction_bdd
        self.abstraction_sdd = args.abstraction_sdd
        self.no_boolean_mapping = args.no_boolean_mapping
        self.dump_abstraction = args.dump_abstraction
        self.print_mapping = args.print_mapping
        self.count_models = args.count_models
        self.count_vertices = args.count_vertices
        self.count_nodes = args.count_nodes
        self.save_lemmas = args.save_lemmas
        self.load_lemmas = args.load_lemmas
        self.verbose = args.verbose
        self.load_details = args.load_details
        self.abstraction_dDNNF = args.abstraction_dDNNF
        self.tdDNNF = args.tdDNNF
        self.abstraction_dDNNF_output = args.abstraction_dDNNF_output
        self.tdDNNF_output = args.tdDNNF_output
        self.keep_c2d_temp = args.keep_c2d_temp
        self.no_dDNNF_to_pysmt = args.no_dDNNF_to_pysmt
        self.dDNNF_compiler = args.dDNNF_compiler
        self.save_tbdd = args.save_tbdd
        self.save_abstraction_bdd = args.save_abstraction_bdd
        self.save_tsdd = args.save_tsdd
        self.save_abstraction_sdd = args.save_abstraction_sdd


def get_args() -> Options:
    """Reads the args from the command line"""
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--tsdd",
        help="Generate the T-SDD of the formula",
        action="store_true")
    parser.add_argument(
        "-v", "--verbose",
        help="Get output on stdout during computation",
        action="store_true"
    )
    parser.add_argument(
        "--xsdd",
        help="Generate the XSDD of the formula",
        action="store_true")
    parser.add_argument(
        "--tbdd",
        help="Generate the T-BDD of the formula",
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
        "--tvtree",
        help="Specify V-Tree kind for T-SDD generation (default is right). Available values: "+str(
            VALID_VTREE),
        type=str,
        choices=VALID_VTREE,
        default="right")
    parser.add_argument(
        "--abstraction_vtree",
        help="Specify V-Tree kind for Abstraction-SDD generation (default is right). Available values: "+str(
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
        "--tvtree_output",
        help="Specify a .dot or .svg file to save the vtree of the T-SDD (by default the vtree is not saved)",
        type=str)
    parser.add_argument(
        "--abstraction_vtree_output",
        help="Specify a .dot or .svg file to save the vtree of the Abstraction SDD (by default the vtree is not saved)",
        type=str)
    parser.add_argument(
        "-i", "--input",
        help="Specify a file from witch to read the formula",
        type=str)
    parser.add_argument(
        "--tsdd_output",
        help="Specify a .dot or .svg file to output the T-SDD",
        type=str)
    parser.add_argument(
        "--tbdd_output",
        help="Specify a .dot or .svg file to output the T-BDD",
        type=str)
    parser.add_argument(
        "--abstraction_sdd_output",
        help="Specify a .dot or .svg file to output the Abstraction-SDD",
        type=str)
    parser.add_argument(
        "--abstraction_bdd_output",
        help="Specify a .dot or .svg file to output the Abstraction-BDD",
        type=str)
    parser.add_argument(
        "--ldd_output",
        help="Specify a .dot or .svg file to output the LDD",
        type=str)
    parser.add_argument(
        "-d", "--details_file",
        help="Specify a .json file to save the computation details",
        type=str)
    parser.add_argument(
        "--load_details",
        help="Specify a .json file to load the computation details from",
        type=str)
    parser.add_argument(
        "--abstraction_bdd",
        help="Build an Abstraction BDD",
        action="store_true")
    parser.add_argument(
        "--abstraction_sdd",
        help="Build an Abstraction SDD",
        action="store_true")
    parser.add_argument(
        "--no_boolean_mapping",
        help="Do not use a boolean mapping to enumerate when computing All SMT with total solver",
        action="store_true")
    parser.add_argument(
        "--dump_abstraction",
        help="Dump the DD or SDD with abstraction labels",
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
        help="Specify a .smt file to save the lemmas obtained from All-SMT. Lemmas can be saved only if not previously loaded",
        type=str)
    parser.add_argument(
        "--load_lemmas",
        help="Specify a .smt file to load lemmas from instead of performing All-SMT",
        type=str)
    parser.add_argument(
        "--abstraction_dDNNF_output",
        help="Specify a .smt file to save the abstraction dDNNF",
        type=str)
    parser.add_argument(
        "--tdDNNF_output",
        help="Specify a .smt file to save the T-dDNNF of the input formula",
        type=str)
    parser.add_argument(
        "--tdDNNF",
        help="Generate the T-dDNNF of the input formula",
        action="store_true")
    parser.add_argument(
        "--abstraction_dDNNF",
        help="Generate the  Abstraction dDNNF of the input formula",
        action="store_true")
    parser.add_argument(
        "--keep_c2d_temp",
        help="Keep the temporary files generated by the c2d compiler in the specified folder",
        type=str)
    parser.add_argument(
        "--no_dDNNF_to_pysmt",
        help="Do not convert the dDNNF to pysmt formula",
        action="store_true")
    parser.add_argument(
        "--dDNNF_compiler",
        help=f"Select the compiler to use for dDNNF compilation among {VALID_DDNNF_COMPILER}. Default: c2d",
        type=str,
        choices=VALID_DDNNF_COMPILER,
        default="c2d")
    parser.add_argument(
        "--save_tbdd",
        help="Save the T-BDD data inside the specified folder",
        type=str)
    parser.add_argument(
        "--save_abstraction_bdd",
        help="Save the Abstraction-BDD data inside the specified folder",
        type=str)
    parser.add_argument(
        "--save_tsdd",
        help="Save the T-SDD data inside the specified folder",
        type=str)
    parser.add_argument(
        "--save_abstraction_sdd",
        help="Save the Abstraction-SDD data inside the specified folder",
        type=str)
    # parser.add_argument(
    #     "--check_eq",
    #     help="Check the T-equivalence of the T-agnostic DD with the T-formula phi",
    #     action="store_true")
    args = parser.parse_args()
    return Options(args)
