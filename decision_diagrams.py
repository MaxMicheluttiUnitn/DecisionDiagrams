from pysmt.fnode import FNode
from pysdd.sdd import SddManager, Vtree
import time
from dd.autoref import BDD
from string_generator import sequential_string_generate
import formula


def compute_sdd(phi:FNode, vtree_type=None, output_file = None):
    if vtree_type is None:
        vtree_type = "right"
    if output_file is None:
        output_file = "sdd.dot"
    start_time = time.time()
    print("Building V-Tree...")
    atoms = formula.get_atoms(phi)
    var_count = len(atoms)
    # for now just use appearance order in phi
    var_order =  list(range(1, var_count + 1))
    vtree = Vtree(var_count, var_order, vtree_type)
    print("V-Tree built in ",time.time()-start_time," seconds")
    

    start_time = time.time()
    print("Building SDD...")
    manager = SddManager.from_vtree(vtree)
    sdd_literals = [manager.literal(i) for i in range(1, var_count + 1)]

    atom_literal_map = dict(zip(atoms, sdd_literals))
    
    sdd_formula = compute_sdd_formula(phi,atom_literal_map)
    print("SDD build in ",time.time()-start_time," seconds")

    start_time = time.time()
    print("Saving SDD...")
    with open(output_file, "w") as out:
        print(sdd_formula.dot(), file=out)
        print("SDD saved as sdd.dot in ",time.time()-start_time," seconds")


def compute_sdd_formula(phi:FNode,mapping:dict[FNode,int]):
    return compute_sdd_formula_recursive(phi,mapping)

def compute_sdd_formula_recursive(source:FNode,mapping:dict[FNode,int]):
    if source.is_not():
        result = ~ compute_sdd_formula_recursive(source.args()[0],mapping)
        return result
    if not source.is_bool_op():
        return mapping[source]
    subformulae = source.args()
    translated_subformulae = list(map(lambda x: compute_sdd_formula_recursive(x,mapping),subformulae))
    if len(translated_subformulae) <= 0:
        raise Exception("Boolean operator without children found")
    if source.is_and():
        if len(translated_subformulae) == 1:
            return translated_subformulae[0]
        result = translated_subformulae[0] & translated_subformulae[1]
        for i in range(2,len(translated_subformulae)):
            result = result & translated_subformulae[i]
        return result
    if source.is_or():
        if len(translated_subformulae) == 1:
            return translated_subformulae[0]
        result = translated_subformulae[0] | translated_subformulae[1]
        for i in range(2,len(translated_subformulae)):
            result = result | translated_subformulae[i]
        return result
    if source.is_iff():
        if len(translated_subformulae) == 1:
            return translated_subformulae[0]
        result = (translated_subformulae[0] & translated_subformulae[1]) | ((~ translated_subformulae[0]) & (~ translated_subformulae[1]))
        return result

def compute_bdd(phi:FNode, output_file = None):
    if output_file is None:
        output_file = "bdd.svg"
    bdd = BDD()
    atoms = formula.get_atoms(phi)
    mapping = {}
    for atom in atoms:
        mapping[atom]=sequential_string_generate()
    all_values = []
    for value in mapping.values():
        all_values.append(value)
    bdd.declare(*all_values)
    root = compute_bdd_formula(phi,mapping,bdd)
    bdd.collect_garbage()
    #bdd.dump("bdd.svg",filetype='svg',roots=[root])
    bdd.dump(output_file,filetype='svg')

def compute_bdd_formula(phi:FNode,mapping:dict[FNode,str],handler:BDD):
    return compute_bdd_formula_recursive(phi,mapping,handler)

def compute_bdd_formula_recursive(source:FNode,mapping:dict[FNode,str],handler:BDD):
    if source.is_not():
        result = ~ compute_bdd_formula_recursive(source.args()[0],mapping,handler)
        return result
    if not source.is_bool_op():
        return handler.add_expr(mapping[source])
    subformulae = source.args()
    translated_subformulae = list(map(lambda x: compute_bdd_formula_recursive(x,mapping,handler),subformulae))
    if len(translated_subformulae) <= 0:
        raise Exception("Boolean operator without children found")
    if source.is_and():
        if len(translated_subformulae) == 1:
            return translated_subformulae[0]
        result = translated_subformulae[0] & translated_subformulae[1]
        for i in range(2,len(translated_subformulae)):
            result = result & translated_subformulae[i]
        return result
    if source.is_or():
        if len(translated_subformulae) == 1:
            return translated_subformulae[0]
        result = translated_subformulae[0] | translated_subformulae[1]
        for i in range(2,len(translated_subformulae)):
            result = result | translated_subformulae[i]
        return result
    if source.is_iff():
        if len(translated_subformulae) == 1:
            return translated_subformulae[0]
        result = (translated_subformulae[0] & translated_subformulae[1]) | ((~ translated_subformulae[0]) & (~ translated_subformulae[1]))
        return result


if __name__ == "__main__":
    phi = formula.get_phi()
    compute_bdd(phi)