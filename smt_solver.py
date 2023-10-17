from pysmt.shortcuts import Solver
import mathsat
from pysmt.fnode import FNode
from typing import List

SAT = True
UNSAT = False

last_phi=None
tlemmas=[]
models=[]

def _allsat_callback(model, converter, models):
    py_model = {converter.back(v) for v in model}
    models.append(py_model)
    return 1

def check_sat(phi:FNode) -> bool:
    global last_phi
    global tlemmas
    global models

    last_phi = phi
    
    solver_options_dict = {
        "dpll.allsat_minimize_model": "false",  # - truth assignment totali
        # "dpll.allsat_allow_duplicates": "false", # - per produrre truth assignment non necessariamente disjoint.
        #                                          # ha senso metterla a true solo se minimize_model=true.
        "preprocessor.toplevel_propagation": "false",  # - necessari per disabilitare step di preprocessing fatti
        "preprocessor.simplification": "0",  # da mathsat
        "dpll.store_tlemmas": "true",  # - necessario per ottenere t-lemmi
    }

    atoms = phi.get_atoms()

    with Solver("msat", solver_options=solver_options_dict) as solver:
        converter = solver.converter
        solver.add_assertion(phi)
        models = []
        mathsat.msat_all_sat(solver.msat_env(), [converter.convert(a) for a in atoms],
                             callback=lambda model: _allsat_callback(model, converter, models))
        tlemmas = [converter.back(l) for l in mathsat.msat_get_theory_lemmas(solver.msat_env())]
        if len(models) == 0:
            return UNSAT
        return SAT


def get_theory_lemmas() -> List[FNode]:
    global tlemmas
    return tlemmas

def get_models() -> List:
    global models
    return models