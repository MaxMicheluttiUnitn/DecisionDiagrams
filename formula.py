from typing import List
from pysmt.shortcuts import Symbol, REAL, And, Or, Xor
from pysmt.fnode import FNode

def get_phi() -> FNode:
    ' ' 'Returns the default SMT formula\'s root FNode' ' '
    x1, x2, x3, x4 = Symbol("x1", REAL), Symbol("x2", REAL), Symbol("x3", REAL), Symbol("x4", REAL)
    left_xor = Or(x1 > x2, x2 > x1)
    right_xor = Or(x3 > x4, x4 > x3)
    phi = And(left_xor,right_xor,Xor(x1>x4,x4>x1))
    # phi = Xor(x1>x4,x4>x1)
    return phi

def read_phi(filename:str) -> FNode:
    ' ' 'Reads the SMT formula from a file and returns the corresponding root FNode' ' '
    print("Not yet implemented!!! Using standard phi instead!!!")
    return get_phi()

def get_atoms(phi:FNode) -> List[FNode]:
    ' ' 'returns a list of all the atoms in the SMT formula' ' '
    return list(phi.get_atoms())

def add_theory_lemmas(phi:FNode,tlemmas:List[FNode]) -> None:
    ' ' 'Adds theory lemmas to the formula phi as a conjunction' ' '
    phi = And(phi,*tlemmas)

def get_phi_and_lemmas(phi:FNode,tlemmas:List[FNode]) -> FNode:
    ' ' 'Returns a formula that is equivalent to phi and lemmas as an FNode' ' '
    return And(phi,*tlemmas)
