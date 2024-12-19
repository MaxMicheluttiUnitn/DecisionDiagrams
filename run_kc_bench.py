"""module for starting a benchmarking run on the main benchmarks for this project"""
import os
from typing import List

VALID_BENCHS = ["ldd_randgen", "randgen", "qfrdl"]
RUN_TYPES = ["allsmt", "dd", "both", "abstraction"]
VALID_SOLVERS = ["total", "partial", "full_partial",
                 "tabular_total", "tabular_partial"]
VALID_DD = ["tbdd", "tsdd", "tddnnf"]
VALID_ABSTRACT_DD = ["abstraction_bdd",
                     "abstraction_sdd", "abstraction_ddnnf", "ldd"]
VALID_DDNNF_COMPILER = ["c2d", "d4"]

COMPILER_FILE = "knowledge_compiler.py"
# can be changed to "python3" if python3 is the command for python in your system
PYTHON_COMMAND = "python"


def prepare_paths_ldd_randgen(output_folder: str, tmp_folder: str) -> List[str]:
    """prepare the paths for the ldd_randgen benchmark
    and returns the input  files
    Returns:
        List[str]: list of input files
    """
    input_files = []
    if output_folder is not None and not os.path.isdir(f"benchmarks/ldd_randgen/{output_folder}"):
        os.mkdir(f"benchmarks/ldd_randgen/{output_folder}")
    if tmp_folder is not None and not os.path.isdir(f"benchmarks/ldd_randgen/{tmp_folder}"):
        os.mkdir(f"benchmarks/ldd_randgen/{tmp_folder}")
    for dataset in os.listdir("benchmarks/ldd_randgen/data"):
        if tmp_folder is not None and not os.path.isdir(f"benchmarks/ldd_randgen/{tmp_folder}/{dataset}"):
            os.mkdir(f"benchmarks/ldd_randgen/{tmp_folder}/{dataset}")
        if output_folder is not None and not os.path.isdir(f"benchmarks/ldd_randgen/{output_folder}/{dataset}"):
            os.mkdir(f"benchmarks/ldd_randgen/{output_folder}/{dataset}")
        for numbered_folder in os.listdir(f"benchmarks/ldd_randgen/data/{dataset}"):
            if tmp_folder is not None and not os.path.isdir(f"benchmarks/ldd_randgen/{tmp_folder}/{dataset}/{numbered_folder}"):
                os.mkdir(
                    f"benchmarks/ldd_randgen/{tmp_folder}/{dataset}/{numbered_folder}")
            if output_folder is not None and not os.path.isdir(f"benchmarks/ldd_randgen/{output_folder}/{dataset}/{numbered_folder}"):
                os.mkdir(
                    f"benchmarks/ldd_randgen/{output_folder}/{dataset}/{numbered_folder}")
            for filename in os.listdir(f"benchmarks/ldd_randgen/data/{dataset}/{numbered_folder}"):
                if not filename.endswith(".smt2"):
                    continue
                input_files.append(
                    f"benchmarks/ldd_randgen/data/{dataset}/{numbered_folder}/{filename}")
    return input_files


def prepare_paths_randgen(output_folder: str, tmp_folder: str) -> List[str]:
    """prepare the paths for the randgen benchmark
    and returns the input  files
    Returns:
        List[str]: list of input files
    """
    input_files = []
    if output_folder is not None and not os.path.isdir(f"benchmarks/randgen/{output_folder}"):
        os.mkdir(f"benchmarks/randgen/{output_folder}")
    if tmp_folder is not None and not os.path.isdir(f"benchmarks/randgen/{tmp_folder}"):
        os.mkdir(f"benchmarks/randgen/{tmp_folder}")
    for dataset in os.listdir("benchmarks/randgen/data"):
        if tmp_folder is not None and not os.path.isdir(f"benchmarks/randgen/{tmp_folder}/{dataset}"):
            os.mkdir(f"benchmarks/randgen/{tmp_folder}/{dataset}")
        if output_folder is not None and not os.path.isdir(f"benchmarks/randgen/{output_folder}/{dataset}"):
            os.mkdir(f"benchmarks/randgen/{output_folder}/{dataset}")
        for numbered_folder in os.listdir(f"benchmarks/randgen/data/{dataset}"):
            if tmp_folder is not None and not os.path.isdir(f"benchmarks/randgen/{tmp_folder}/{dataset}/{numbered_folder}"):
                os.mkdir(
                    f"benchmarks/randgen/{tmp_folder}/{dataset}/{numbered_folder}")
            if output_folder is not None and not os.path.isdir(f"benchmarks/randgen/{output_folder}/{dataset}/{numbered_folder}"):
                os.mkdir(
                    f"benchmarks/randgen/{output_folder}/{dataset}/{numbered_folder}")
            for filename in os.listdir(f"benchmarks/randgen/data/{dataset}/{numbered_folder}"):
                if not filename.endswith(".smt2"):
                    continue
                input_files.append(
                    f"benchmarks/randgen/data/{dataset}/{numbered_folder}/{filename}")
    return input_files


def prepare_paths_qfrdl(output_folder: str, tmp_folder: str) -> List[str]:
    """prepare the paths for the smtlib QF RDL benchmark
    and returns the input  files
    Returns:
        List[str]: list of input files
    """
    input_files = []
    if output_folder is not None and not os.path.isdir(f"benchmarks/smtlib/{output_folder}"):
        os.mkdir(f"benchmarks/smtlib/{output_folder}")
        os.mkdir(f"benchmarks/smtlib/{output_folder}/non-incremental")
        os.mkdir(f"benchmarks/smtlib/{output_folder}/non-incremental/QF_RDL")
    if tmp_folder is not None and not os.path.isdir(f"benchmarks/smtlib/{tmp_folder}"):
        os.mkdir(f"benchmarks/smtlib/{tmp_folder}")
        os.mkdir(f"benchmarks/smtlib/{tmp_folder}/non-incremental")
        os.mkdir(f"benchmarks/smtlib/{tmp_folder}/non-incremental/QF_RDL")
    for dataset in os.listdir("benchmarks/smtlib/data/non-incremental/QF_RDL"):
        if output_folder is not None and not os.path.isdir(f"benchmarks/smtlib/{output_folder}/non-incremental/QF_RDL/{dataset}"):
            os.mkdir(
                f"benchmarks/smtlib/{output_folder}/non-incremental/QF_RDL/{dataset}")
        if tmp_folder is not None and not os.path.isdir(f"benchmarks/smtlib/{tmp_folder}/non-incremental/QF_RDL/{dataset}"):
            os.mkdir(
                f"benchmarks/smtlib/{tmp_folder}/non-incremental/QF_RDL/{dataset}")
        for filename in os.listdir(f"benchmarks/smtlib/data/non-incremental/QF_RDL/{dataset}"):
            if not filename.endswith(".smt2"):
                continue
            input_files.append(
                f"benchmarks/smtlib/data/non-incremental/QF_RDL/{dataset}/{filename}")
    return input_files


def main() -> None:
    """main function for running the benchmarking script"""
    print(VALID_BENCHS)
    bench_source = input("Enter the benchmark name: ")
    bench_source = bench_source.strip().lower()
    if bench_source not in VALID_BENCHS:
        print("Invalid benchmark source")
        return
    print(RUN_TYPES)
    run_type = input("Enter the run type: ")
    run_type = run_type.strip().lower()
    if run_type not in RUN_TYPES:
        print("Invalid run type")
        return
    solver_type = None
    dd_type = None
    tmp_folder = None
    output_folder = None
    ddnnf_compiler = None
    save_dd = False
    if run_type != "abstraction":
        tmp_folder = input("Enter the temporary folder name: ")
    if run_type == "allsmt" or run_type == "both":
        print(VALID_SOLVERS)
        solver_type = input("Enter the solver type: ")
        solver_type = solver_type.strip().lower()
        if solver_type not in VALID_SOLVERS:
            print("Invalid solver type")
            return
    if run_type == "dd" or run_type == "both":
        print(VALID_DD)
        dd_type = input("Enter the dd type: ")
        dd_type = dd_type.strip().lower()
        if dd_type not in VALID_DD:
            print("Invalid dd type")
            return
        output_folder = input("Enter the output folder name: ")
        if dd_type == "tbdd" or dd_type == "tsdd":
            answer = input(
                "Do you want to serialize the generated DDs? (y/n): ")
            answer = answer.strip().lower()
            if answer == "y":
                save_dd = True
        if dd_type == "tddnnf":
            print(VALID_DDNNF_COMPILER)
            ddnnf_compiler = input("Select a tdDNNF compiler: ")
            if ddnnf_compiler not in VALID_DDNNF_COMPILER:
                print("Invalid dDNNF compiler")
                return
    if run_type == "abstraction":
        print(VALID_ABSTRACT_DD)
        dd_type = input("Enter the dd type: ")
        dd_type = dd_type.strip().lower()
        if dd_type not in VALID_ABSTRACT_DD:
            print("Invalid dd type")
            return
        if dd_type == "abstraction_bdd" or dd_type == "abstraction_sdd":
            answer = input(
                "Do you want to serialize the generated DDs? (y/n): ")
            answer = answer.strip().lower()
            if answer == "y":
                save_dd = True
        if dd_type == "abstraction_ddnnf":
            tmp_folder = input("Enter the tmp folder name: ")
            print(VALID_DDNNF_COMPILER)
            ddnnf_compiler = input("Select a tdDNNF compiler: ")
            if ddnnf_compiler not in VALID_DDNNF_COMPILER:
                print("Invalid dDNNF compiler")
                return
        output_folder = input("Enter the output folder name: ")

    # print a summary of selected options
    print("\n\n\nSUMMARY")
    print("Benchmark source:", bench_source)
    print("Run type:", run_type)
    print("Solver type:", solver_type)
    print("DD type:", dd_type)
    print("Temporary folder:", tmp_folder)
    print("Output folder:", output_folder)
    print("dDNNF compiler: ", ddnnf_compiler)
    print("Save DDs: ", save_dd)
    # ask confirmation
    is_ok = input("Is this correct? (y/n): ")
    is_ok = is_ok.strip().lower()
    if is_ok != "y":
        return

    # prepare for the run
    if bench_source == "ldd_randgen":
        input_files = prepare_paths_ldd_randgen(output_folder, tmp_folder)
    elif bench_source == "randgen":
        input_files = prepare_paths_randgen(output_folder, tmp_folder)
    elif bench_source == "qfrdl":
        input_files = prepare_paths_qfrdl(output_folder, tmp_folder)
    else:
        raise ValueError("Invalid benchmark source")

    # run the benchmarks
    for input_file in input_files:
        print(f"Running {input_file}...")
        # abstraction
        if run_type == "abstraction":
            result = 0
            output_folder_path = input_file.replace("data", output_folder)
            output_file = output_folder_path.replace(".smt2", ".json")
            save_dd_str = ""
            if os.path.exists(output_file):
                print(f"{output_file} already exists. Skipping...")
                continue
            if dd_type == "abstraction_bdd":
                if save_dd:
                    save_dd_folder = output_folder_path.replace(".smt2", "")
                    save_dd_str = f"--save_abstraction_bdd {save_dd_folder}_abstraction_bdd"
                result = os.system(
                    f"timeout 3600s {PYTHON_COMMAND} {COMPILER_FILE} -v -i {input_file} --count_nodes --count_models --abstraction_bdd -d {output_file} {save_dd_str}")
            elif dd_type == "abstraction_sdd":
                if save_dd:
                    save_dd_folder = output_folder_path.replace(".smt2", "")
                    save_dd_str = f"--save_abstraction_sdd {save_dd_folder}_abstraction_sdd"
                result = os.system(
                    f"timeout 3600s {PYTHON_COMMAND} {COMPILER_FILE} -v -i {input_file} --abstraction_sdd --count_nodes --count_models -d {output_file} --abstraction_vtree balanced {save_dd_str}")
            elif dd_type == "abstraction_ddnnf":
                tmp_folder_path = output_folder_path.replace(
                    ".smt2", f"_{ddnnf_compiler}")
                os.system(
                    f"{PYTHON_COMMAND} {COMPILER_FILE} -v -i {input_file} --abstraction_dDNNF -d {output_file} --no_dDNNF_to_pysmt --keep_c2d_temp {tmp_folder_path} --dDNNF_compiler {ddnnf_compiler}")
            elif dd_type == "ldd":
                result = os.system(
                    f"timeout 3600s {PYTHON_COMMAND} {COMPILER_FILE} -v -i {input_file} --ldd --ldd_theory TVPI --count_models --count_nodes -d {output_file}")
            if result != 0:
                print(f"Abstraction DD compilation timed out for {input_file}")
                with open(output_file, "w", encoding='utf8') as f:
                    f.write("{\"timeout\": \"DD\"}")
                continue

        # allsmt only
        elif run_type == "allsmt" or run_type == "both":
            tmp_lemma_file = input_file.replace("data", tmp_folder)
            tmp_json_file = tmp_lemma_file.replace(".smt2", ".json")
            print(f"Running allsmt on {input_file}...")
            if os.path.exists(tmp_json_file):
                print(f"{tmp_json_file} already exists. Skipping...")
                continue
            os.system(
                f"timeout 3600s {PYTHON_COMMAND} {COMPILER_FILE} -v -i {input_file} --save_lemmas {tmp_lemma_file} --solver partial -d {tmp_json_file} --count_models")

        # dd compilation only
        elif run_type == "dd" or run_type == "both":
            result = 0
            tmp_lemma_file = input_file.replace("data", tmp_folder)
            tmp_json_file = tmp_lemma_file.replace(".smt2", ".json")
            output_folder_path = input_file.replace("data", output_folder)
            output_file = output_folder_path.replace(".smt2", ".json")
            save_dd_str = ""
            print(f"Running DD compilation on {input_file}...")

            # check if allsmt timed out
            if not os.path.exists(tmp_json_file):
                print(f"{tmp_json_file} does not exist. AllSMT ended in timeout.")
                with open(output_file, "w", encoding='utf8') as f:
                    f.write("{\"timeout\": \"ALL SMT\"}")
                continue

            if dd_type == "tbdd":
                if save_dd:
                    save_dd_folder = output_folder_path.replace(".smt2", "")
                    save_dd_str = f"--save_tbdd {save_dd_folder}_tbdd"
                result = os.system(
                    f"timeout 3600s {PYTHON_COMMAND} {COMPILER_FILE} -v -i {input_file} --load_lemmas {tmp_lemma_file} --load_details {tmp_json_file} --tbdd --count_nodes --count_models -d {output_file} {save_dd_str}")
            elif dd_type == "tsdd":
                if save_dd:
                    save_dd_folder = output_folder_path.replace(".smt2", "")
                    save_dd_str = f"--save_tbdd {save_dd_folder}_tsdd"
                result = os.system(
                    f"timeout 3600s {PYTHON_COMMAND} {COMPILER_FILE} -v -i {input_file} --load_lemmas {tmp_lemma_file} --load_details {tmp_json_file}  --tsdd --count_nodes --count_models -d {output_file} --tvtree balanced {save_dd_str}")
            elif dd_type == "tddnnf":
                tmp_ddnnf_folder = output_folder_path.replace(
                    ".smt2", f"_{ddnnf_compiler}")
                os.system(
                    f"{PYTHON_COMMAND} {COMPILER_FILE} -v -i {input_file} --load_lemmas {tmp_lemma_file} --load_details {tmp_json_file} --tdDNNF -d {output_file} --no_dDNNF_to_pysmt --keep_c2d_temp {tmp_ddnnf_folder} --dDNNF_compiler {ddnnf_compiler}")

            if result != 0:
                print(f"DD compilation timed out for {input_file}")
                with open(output_file, "w", encoding='utf8') as f:
                    f.write("{\"timeout\": \"DD\"}")
                continue

        print(f"Finished running {input_file}")

    print("ALL  RUNS COMPLETED")
    print("\n\n\nSUMMARY")
    print("Benchmark source:", bench_source)
    print("Run type:", run_type)
    print("Solver type:", solver_type)
    print("DD type:", dd_type)
    print("Temporary folder:", tmp_folder)
    print("Output folder:", output_folder)


if __name__ == "__main__":
    main()
