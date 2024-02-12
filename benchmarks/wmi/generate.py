import argparse as ap
import os

import pysmt.shortcuts
import wmibench.synthetic.synthetic_structured as struct_bench

SEED = 666
SIZE = "1:20"


def _parse_interval(s: str) -> tuple[int, int]:
    try:
        a, b = tuple(map(int, s.split(":")))
        return a, b
    except ValueError:
        raise ap.ArgumentTypeError("Interval must be of the form 'a:b' where a and b are integers")


def parse_args() -> ap.Namespace:
    parser = ap.ArgumentParser(description="Generate structured benchmarks")
    parser.add_argument("--size", type=_parse_interval, default=SIZE)
    parser.add_argument("--output_folder", required=True, help="Output folder")
    return parser.parse_args()


def generate_struct_bench(size: tuple[int, int], output_folder: str) -> None:
    # get max number of digits and pad with 0s the filename to have a consistent ordering
    min_size, max_size = size
    max_digits = len(str(max_size))
    filename_template = "{{:s}}_{{:0{}}}.smt2".format(max_digits)
    for t in ["xor", "mutex", "click"]:
        output_folder_t = os.path.join(output_folder, t)
        print(f"Generating benchmarks for {t} in {output_folder_t}")
        os.makedirs(output_folder_t, exist_ok=True)
        pg = struct_bench.get_problem(t)
        for size in range(min_size, max_size + 1):
            filename = filename_template.format(t, size)
            density = pg(size)
            phi = density.support
            pysmt.shortcuts.write_smtlib(phi, os.path.join(output_folder_t, filename))
    print("Done!")


def main() -> None:
    args = parse_args()
    generate_struct_bench(args.size, args.output_folder)


if __name__ == "__main__":
    main()
