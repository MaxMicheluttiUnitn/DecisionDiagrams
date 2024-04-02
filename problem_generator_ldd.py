import argparse
import os
import random
import sys
import time
from math import log10
from os import path

from pysmt.shortcuts import Symbol, Or, Not, And, Iff, write_smtlib, LT, Real, Bool, Times, Plus, is_sat, Int
from pysmt.typing import BOOL, REAL, INT

DESCRIPTION = '''Generates random SMT(LRA) formulas.
        
The boolean variables are named A0, A1, ...
The real variables are named x0, x1, ...
The domains of the real variables are [0, 1]
The LRA atoms are linear inequalities of the form
    c1 * x1 + c2 * x2 + ... + cn * xn < b
where c1, ..., cn are random coefficients in [-1, 1] and b is a random integer in [-n, n].'''


def arg_positive_0(value: str):
    """checks if the integer is non negative"""
    value = int(value)
    if value < 0:
        raise argparse.ArgumentTypeError(
            f'Expected non-negative integer, found {value}')
    return value


def arg_positive(value: str) -> int:
    """asserts positivity of the value"""
    int_value = int(value)
    if int_value <= 0:
        raise argparse.ArgumentTypeError(
            f'Expected positive integer (no 0), found {value}')
    return int_value


def arg_probability(value: str) -> float:
    """computes the probability for an arg"""
    fvalue = float(value)
    if fvalue < 0 or fvalue > 1:
        raise argparse.ArgumentTypeError(
            f'Expected probability in [0, 1], found {value}')
    return fvalue


def check_output(output_dir: str, output_file: str):
    """checks if the output directory exists and the file does not already exist"""
    if not path.exists(output_dir):
        print(f"'{output_dir}' does not exists")
        sys.exit(1)

    if path.exists(output_file):
        print(f"'{output_file}' already exists. Remove it and retry")
        sys.exit(1)


class FormulaGenerator:
    """a class to generate SMT formulas"""
    TEMPL_REALS = "x{}"
    TEMPL_BOOLS = "A{}"

    # maximum (absolute) value a variable can take
    DOMAIN_BOUNDS = [0, 1]

    def __init__(self, n_bools, n_reals, seed):
        assert n_bools + n_reals > 0

        # initialize the real/boolean variables
        self.reals = []
        for i in range(n_reals):
            self.reals.append(Symbol(self.TEMPL_REALS.format(i), INT))
        self.bools = []
        for i in range(n_bools):
            self.bools.append(Symbol(self.TEMPL_BOOLS.format(i), BOOL))

        self.domain_bounds = dict()
        # set the seed number, if specified
        random.seed(seed)

    def generate_random_formula(self, depth, operators, neg_prob=0.5, theta=0.5):
        """
        Generate a random formula of the given depth.
        :param depth: the depth of the formula
        :param operators: a dictionary of operators and their weights
        :param neg_prob: the probability of negating a formula
        :param theta: the probability of generating a Boolean atom rather than a LRA atom
        """
        domain = []
        for r_var in self.reals:
            domain.append(r_var >= self.DOMAIN_BOUNDS[0])
            domain.append(r_var <= self.DOMAIN_BOUNDS[1])
        formula = Bool(False)
        while not is_sat(formula):
            formula = And(*domain, self._random_formula(depth,
                          operators, neg_prob, theta))
        return formula

    def _random_formula(self, depth, operators, neg_prob, theta):
        if depth <= 0:
            leaf = self._random_atom(theta)
            if random.random() < neg_prob:
                leaf = Not(leaf)
            return leaf
        else:
            operator = random.choices(
                list(operators.keys()), weights=list(operators.values()))[0]

            left = self._random_formula(depth - 1, operators, neg_prob, theta)
            right = self._random_formula(depth - 1, operators, neg_prob, theta)
            node = operator(left, right)
            negate = random.random() < neg_prob
            if negate:
                node = Not(node)
            return node

    def _random_atom(self, theta=0.5):
        if len(self.bools) == 0 or (len(self.reals) > 0 and random.random() < theta):
            return self._random_inequality()
        else:
            return self._random_boolean()

    def _random_boolean(self):
        return random.choice(self.bools)

    def _random_inequality(self, minsize=None, maxsize=2):
        n_reals = len(self.reals)
        minsize = max(1, minsize) if minsize else 1
        maxsize = min(maxsize, n_reals) if maxsize else n_reals
        size = random.randint(minsize, maxsize)
        r_vars = random.sample(self.reals, size)
        monomials = []
        for r_var in r_vars:
            coefficient = self._random_coefficient(-1, 1)
            monomials.append(Times(coefficient, r_var))

        bound = self._random_coefficient(-len(r_vars), len(r_vars))
        return LT(Plus(monomials), bound)

    @staticmethod
    def _random_coefficient(min_value=-1, max_value=1):
        # coefficient = 0
        # while coefficient == 0:
        #     coefficient = random.uniform(min_value, max_value)
        # return Real(coefficient)
        return Int(random.choice([1,-1]))


def parse_args():
    """parse arguments with arg parser library"""
    parser = argparse.ArgumentParser(
        description=DESCRIPTION, formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument('-o', '--output', default=os.getcwd(),
                        help='Folder where all models will be created (default: cwd)')
    parser.add_argument('-b', '--booleans', default=3, type=arg_positive_0,
                        help='Maximum number of bool variables (default: 3)')
    parser.add_argument('-r', '--reals', default=3, type=arg_positive_0,
                        help='Maximum number of real variables (default: 3)')
    parser.add_argument('-t', '--theta', default=0.5, type=arg_probability,
                        help='Probability of generating a Boolean atom rather than a LRA atom (default: 0.5)')
    parser.add_argument('-d', '--depth', default=3, type=arg_positive,
                        help='Depth of the formula tree (default: 3)')
    parser.add_argument('--xnnf', action='store_true', default=False,
                        help='Set this flag to generate formulas in XNNF, i.e. formulas where negations occur only '
                             'at literal level (default: False)')
    parser.add_argument('-m', '--models', default=20, type=arg_positive,
                        help='Number of model files (default: 20)')
    parser.add_argument('-s', '--seed', type=arg_positive_0, required=True,
                        help='Random seed')

    return parser.parse_args()


def main():
    """main function for SMT generation"""
    args = parse_args()

    output_dir = f'ldd_phi_problems_b{args.booleans}_r{args.reals}_d{args.depth}_m{args.models}_s{args.seed}'
    output_dir = path.join(args.output, output_dir)

    check_output(args.output, output_dir)
    os.mkdir(output_dir)

    # init generator
    generator = FormulaGenerator(args.booleans, args.reals, args.seed)

    # generate formulas
    print("Starting creating problems")
    time_start = time.time()
    digits = int(log10(args.models)) + 1
    template = "ldd_phi_b{b}_d{d}_r{r}_s{s}_{templ}.smt2".format(b=args.booleans, r=args.reals, d=args.depth, s=args.seed,
                                                         templ="{n:0{d}}")

    operators = {
        Iff: 1 / 10,
        Or: 9 / 20,
        And: 9 / 20,
    }
    weights_sum = sum(operators.values())
    for k in operators:
        operators[k] /= weights_sum
    neg_prob = 0.0 if args.xnnf else 0.5

    for i in range(args.models):
        problem = generator.generate_random_formula(
            args.depth, operators, neg_prob, args.theta)
        if(i+1<10):
            actual_output_folder = output_dir+'/0'+str(i+1)
        else:
            actual_output_folder = output_dir+'/'+str(i+1)
        os.mkdir(actual_output_folder)
        file_name = path.join(actual_output_folder, template.format(n=i + 1, d=digits))
        write_smtlib(problem, file_name)
        print("\r" * 100, end='')
        print(f"Problem {i+1}/{args.models}", end='')

    print()
    time_end = time.time()
    seconds = time_end - time_start
    print("Done! {:.3f}s".format(seconds))


if __name__ == '__main__':
    main()
