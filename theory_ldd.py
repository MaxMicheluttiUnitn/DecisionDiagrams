"""LDD handling module"""
import time
from pysmt.fnode import FNode
from dd import ldd

def compute_ldd(phi: FNode,
                     output_file: str | None = None,
                     computation_logger: any = {}):
    '''Computes the LDD for the boolean formula phi and saves it on a file'''
    print("LDD generation")
    raise NotImplementedError()

    # BUILDING LDD
    # start_time = time.time()
    # print("Building LDD...")
    # ldd = ldd.LDD()
    # elapsed_time = (time.time() - start_time)
    # print("LDD for phi built in ", elapsed_time, " seconds")
    # computation_logger["LDD"]["DD building time"] = elapsed_time