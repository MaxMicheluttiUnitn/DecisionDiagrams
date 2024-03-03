"""XSDD generation module"""
from pysmt.fnode import FNode
from pysmt.shortcuts import BOOL, REAL, Real, Times, INT
from pywmi.domain import Domain
from pywmi import XsddEngine

from formula import get_symbols
from walker_xsdd import XsddParser

def compute_xsdd(phi: FNode,computation_logger: any = {}):
    '''computing xsdd'''
    symbols = get_symbols(phi)

    boolean_symbols = []
    real_symbols = []
    # real_bounds=[]

    for symbol in symbols:
        if symbol.get_type() == BOOL:
            boolean_symbols.append("xsdd_"+str(symbol))
        elif symbol.get_type() == REAL:
            real_symbols.append("xsdd_"+str(symbol))
        elif symbol.get_type() == INT:
            real_symbols.append("xsdd_"+str(symbol))
            # just putting very big bounds to let not limit the variable
            # real_bounds.append((-1000000,1000000))

    # bounds are necesssary (XSDD are designed for WMI), so I just put them very big
    xsdd_domain = Domain.make(
        boolean_symbols, real_symbols, real_bounds=(-1000000, 1000000))

    xsdd_boolean_symbols = xsdd_domain.get_bool_symbols()
    xsdd_real_symbols = xsdd_domain.get_real_symbols()
    weight_function = Times(
        Real(2), xsdd_real_symbols[0], xsdd_real_symbols[1])

    walker = XsddParser(boolean_symbols, xsdd_boolean_symbols,
                        real_symbols, xsdd_real_symbols)
    xsdd_support: FNode = walker.walk(phi)

    xsdd_engine = XsddEngine(xsdd_domain, xsdd_support, weight_function)

    # _, xsdd_support, literals = extract_and_replace_literals(xsdd_support)
    # xsdd_sdd = xsdd_engine.get_sdd(
    #     xsdd_support, literals, xsdd_engine.get_vtree(xsdd_support, literals))
    # print(xsdd_sdd)

    # xsdd_other_sdd = compile_to_sdd(xsdd_support, literals, None)

    # with open('sdd_00.dot', 'w') as out:
    #     out.write(xsdd_sdd.dot())

    # with open('sdd_other_00.dot', 'w') as out:
    #     out.write(xsdd_other_sdd.dot())

    print(xsdd_engine.compute_volume(add_bounds=False))