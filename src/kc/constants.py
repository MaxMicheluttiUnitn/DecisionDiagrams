"""module that defines all constants for the Knowledge Compiler

If you want to extend this tool, please add your constants here"""
from theorydd.constants import VALID_VTREE, VALID_LDD_THEORY, VALID_SOLVER as _LIBRARY_SOLVERS # pylint: disable=unused-import

# load environment variables
from dotenv import load_dotenv as _load_env
_load_env()

# ------------------- OPTIONS -------------------

# VALID SOLVERS
# if you want to add new solvers, please add them here
VALID_SOLVER = _LIBRARY_SOLVERS + []

# VALID DDNNF COMPILERS
# if you want to add new dDNNF compilers, please add them here
VALID_DDNNF_COMPILER = ["c2d", "d4"]
