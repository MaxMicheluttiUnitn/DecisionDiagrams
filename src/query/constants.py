"""constants for queries"""

import os

from dotenv import load_dotenv as _load_dotenv

_load_dotenv()
DDNNF_CONDITION_PATH = os.getenv("DDNNF_CONDITION_PATH")
if DDNNF_CONDITION_PATH is not None and os.path.isfile(DDNNF_CONDITION_PATH) and not DDNNF_CONDITION_PATH.startswith("."):
    if DDNNF_CONDITION_PATH.startswith("/"):
        DDNNF_CONDITION_PATH = f".{DDNNF_CONDITION_PATH}"
    else:
        DDNNF_CONDITION_PATH = f"./{DDNNF_CONDITION_PATH}"

DECDNNF_PATH = os.getenv("DDNNF_CONDITION_PATH")
if DECDNNF_PATH is not None and os.path.isfile(DECDNNF_PATH) and not DECDNNF_PATH.startswith("."):
    if DECDNNF_PATH.startswith("/"):
        DECDNNF_PATH = f".{DECDNNF_PATH}"
    else:
        DECDNNF_PATH = f"./{DECDNNF_PATH}"

TRANSLATED_FILE = "translation_to_d4.nnf"
C2D_DDNNF_FILE = "dimacs.cnf.nnf"
D4_DDNNF_FILE = "compilation_output.nnf"

CONDITION_D4_OUTPUT_OPTION = "-o_d4"
CONDITION_C2D_OUTPUT_OPTION = "-o_c2d"
CONDITION_DDNNF_OUTPUT_OPTION = "-o"

TEPORARY_CONDITION_FILE = "temp_condition.nnf"
