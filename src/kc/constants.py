"""module that defines all constants for the Knowledge Compiler"""
import os
import re
from theorydd.constants import VALID_VTREE, VALID_LDD_THEORY, VALID_SOLVER as _LIBRARY_SOLVERS

from dotenv import load_dotenv as _load_env
_load_env()

VALID_SOLVER = _LIBRARY_SOLVERS + ["tabular_partial", "tabular_total"]

VALID_DDNNF_COMPILER = ["c2d", "d4"]

# load c2d executable location from dotenv
_C2D_EXECUTABLE = os.getenv("C2D_BINARY")

# fix command to launch c2d compiler
if _C2D_EXECUTABLE is not None and os.path.isfile(_C2D_EXECUTABLE) and not _C2D_EXECUTABLE.startswith("."):
    if _C2D_EXECUTABLE.startswith("/"):
        _C2D_EXECUTABLE = f".{_C2D_EXECUTABLE}"
    else:
        _C2D_EXECUTABLE = f"./{_C2D_EXECUTABLE}"

# D4 NODES
_D4_AND_NODE = 0
_D4_OR_NODE = 1
_D4_TRUE_NODE = 2
_D4_FALSE_NODE = 3

# D4 REGEX
_RE_NNF_EDGE = re.compile(r"(\d+) (\d+)( .+)? 0")


# load d4 executable location from dotenv
_D4_EXECUTABLE = os.getenv("D4_BINARY")

# fix command to launch d4 compiler
if _D4_EXECUTABLE is not None and os.path.isfile(_D4_EXECUTABLE) and not _D4_EXECUTABLE.startswith("."):
    if _D4_EXECUTABLE.startswith("/"):
        _D4_EXECUTABLE = f".{_D4_EXECUTABLE}"
    else:
        _D4_EXECUTABLE = f"./{_D4_EXECUTABLE}"

# path to the tabular allsmt binary
_TABULAR_ALLSMT_BINARY = os.getenv("TABULAR_ALLSMT_BINARY")
if _TABULAR_ALLSMT_BINARY is not None and isinstance(_TABULAR_ALLSMT_BINARY,str) and not _TABULAR_ALLSMT_BINARY.startswith("."):
    if _TABULAR_ALLSMT_BINARY.startswith("/"):
        _TABULAR_ALLSMT_BINARY = f".{_TABULAR_ALLSMT_BINARY}"
    else:
        _TABULAR_ALLSMT_BINARY = f"./{_TABULAR_ALLSMT_BINARY}"

# regex for tlemmas files
_TLEMMAS_FILE_REGEX = "tlemma_[0-9]+.smt2"
