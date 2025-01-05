"""module that defines all constants for the Knowledge Compiler

If you want to extend this tool, please add your constants here"""
import os
import re
from theorydd.constants import VALID_VTREE, VALID_LDD_THEORY, VALID_SOLVER as _LIBRARY_SOLVERS # pylint: disable=unused-import

# load environment variables
from dotenv import load_dotenv as _load_env
_load_env()

# ------------------- OPTIONS -------------------

# VALID SOLVERS
# if you want to add a new solver, please add it to the list below
VALID_SOLVER = _LIBRARY_SOLVERS + ["tabular_partial", "tabular_total"]

# VALID DDNNF COMPILERS
# if you want to add a new compiler, please add it to the list below
VALID_DDNNF_COMPILER = ["c2d", "d4"]

# ------------------- C2D COMPILER -------------------

# load c2d executable location from dotenv
C2D_EXECUTABLE = os.getenv("C2D_BINARY")

# fix command to launch c2d compiler
if C2D_EXECUTABLE is not None and os.path.isfile(C2D_EXECUTABLE) and not C2D_EXECUTABLE.startswith("."):
    if C2D_EXECUTABLE.startswith("/"):
        C2D_EXECUTABLE = f".{C2D_EXECUTABLE}"
    else:
        C2D_EXECUTABLE = f"./{C2D_EXECUTABLE}"

# ------------------- D4 COMPILER -------------------

# D4 NODES
D4_AND_NODE = 0
D4_OR_NODE = 1
D4_TRUE_NODE = 2
D4_FALSE_NODE = 3

# D4 REGEX
RE_NNF_EDGE = re.compile(r"(\d+) (\d+)( .+)? 0")

# load d4 executable location from dotenv
D4_EXECUTABLE = os.getenv("D4_BINARY")

# fix command to launch d4 compiler
if D4_EXECUTABLE is not None and os.path.isfile(D4_EXECUTABLE) and not D4_EXECUTABLE.startswith("."):
    if D4_EXECUTABLE.startswith("/"):
        D4_EXECUTABLE = f".{D4_EXECUTABLE}"
    else:
        D4_EXECUTABLE = f"./{D4_EXECUTABLE}"

# ------------------- TABULAR ALLSMT -------------------

# path to the tabular allsmt binary
TABULAR_ALLSMT_BINARY = os.getenv("TABULAR_ALLSMT_BINARY")
if TABULAR_ALLSMT_BINARY is not None and isinstance(TABULAR_ALLSMT_BINARY,str) and not TABULAR_ALLSMT_BINARY.startswith("."):
    if TABULAR_ALLSMT_BINARY.startswith("/"):
        TABULAR_ALLSMT_BINARY = f".{TABULAR_ALLSMT_BINARY}"
    else:
        TABULAR_ALLSMT_BINARY = f"./{TABULAR_ALLSMT_BINARY}"

# regex for tlemmas files
TLEMMAS_FILE_REGEX = "tlemma_[0-9]+.smt2"
