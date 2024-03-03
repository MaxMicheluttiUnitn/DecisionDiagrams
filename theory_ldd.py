"""LDD handling module"""
import time
from pysmt.shortcuts import BOOL, INT
from custom_exceptions import UnsupportedSymbolException
import formula
from pysmt.fnode import FNode
from dd import ldd as _ldd
from ldd_walker import LDDWalker

from string_generator import SequentialStringGenerator

def compute_ldd(phi: FNode,
                     output_file: str | None = None,
                     computation_logger: any = {}):
    '''Computes the LDD for the boolean formula phi and saves it on a file'''
    print("LDD generation")
    #raise NotImplementedError()

    # BUILDING LDD
    start_time = time.time()
    print("Building LDD...")
    print(phi)
    symbols = formula.get_symbols(phi)
    boolean_symbols:dict[FNode,str]={}
    integer_symbols:dict[FNode,int]={}
    int_ctr = 1
    str_gen = SequentialStringGenerator()
    for s in symbols:
        if s.get_type() == BOOL:
            boolean_symbols.update({s:str_gen.next_string()})
        elif s.get_type() == INT:
            integer_symbols.update({s:int_ctr})
            int_ctr+=1
        else:
            raise UnsupportedSymbolException(str(s))
    # LDD(Id teoria,#var intere,#var booleane)
    ldd = _ldd.LDD(0,len(integer_symbols.keys()),len(boolean_symbols.keys()))
    walker = LDDWalker(boolean_symbols,integer_symbols,ldd)
    func = walker.walk(phi)
    n_nodes = len(func)
    print("Nodes: ",n_nodes)
    ldd.dump("ldd_out.svg",[func])
    elapsed_time = (time.time() - start_time)
    print("LDD for phi built in ", elapsed_time, " seconds")
    computation_logger["LDD"]["DD building time"] = elapsed_time