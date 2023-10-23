from pysdd.sdd import SddManager
from pysmt.fnode import FNode
from pysmt.walkers import DagWalker 

class SDDWalker(DagWalker):
    '''A walker to translate the DAG formula quickly with memoization into the SDD'''

    def __init__(self, mapping: dict[FNode, int], manager: SddManager, env=None, invalidate_memoization=False):
        DagWalker.__init__(self,env, invalidate_memoization)
        self.mapping = mapping
        self.manager = manager
        return

    def _apply_mapping(self,arg):
        '''applies the mapping when possible, returns None othrwise'''
        if not (self.mapping.get(arg) is None):
            return self.mapping[arg]
        return None

    def walk_and(self, formula: FNode, args, **kwargs):
        '''translate AND node'''
        #pylint: disable=unused-argument
        if len(args) == 1:
            return args[0]
        res = args[0]
        for i in range(1, len(args)):
            res = res & args[i]
        return res

    def walk_or(self, formula: FNode, args, **kwargs):
        '''translate OR node'''
        #pylint: disable=unused-argument
        if len(args) == 1:
            return args[0]
        res = args[0]
        for i in range(1, len(args)):
            res = res | args[i]
        return res
    
    def walk_not(self, formula: FNode, args, **kwargs):
        '''translate NOT node'''
        #pylint: disable=unused-argument
        return ~ args[0]

    def walk_symbol(self,formula: FNode, args, **kwargs):
        '''translate SYMBOL node'''
        #pylint: disable=unused-argument
        return self._apply_mapping(formula)
    
    def walk_bool_constant(self,formula: FNode, args, **kwargs):
        '''translate BOOL const node'''
        #pylint: disable=unused-argument
        value = formula.constant_value()
        if value:
            return self.manager.true()
        return self.manager.false()

    def walk_iff(self, formula, args, **kwargs):
        '''translate IFF node'''
        #pylint: disable=unused-argument
        return (args[0] & args[1]) | ((~ args[0]) & (~ args[1]))

    def walk_implies(self, formula, args, **kwargs):
        '''translate IMPLIES node''' # a -> b === (~ a) v b
        #pylint: disable=unused-argument
        return (~ args[0]) | args[1]
    
    def walk_ite(self, formula, args, **kwargs):
        '''translate ITE node'''
        #pylint: disable=unused-argument
        return ((~ args[0]) | args[1]) & (args[0] | args[2])
    
    def walk_le(self, formula, args, **kwargs):
        '''translate LE node'''
        #pylint: disable=unused-argument
        return self._apply_mapping(formula)

    def walk_lt(self, formula, args, **kwargs):
        '''translate LT node'''
        #pylint: disable=unused-argument
        return self._apply_mapping(formula)
    
    def walk_equals(self, formula, args, **kwargs):
        '''translate EQUALS node'''
        #pylint: disable=unused-argument
        return self._apply_mapping(formula)

    def walk_plus(self, formula, args, **kwargs):
        '''translate PLUS node'''
        #pylint: disable=unused-argument
        return self._apply_mapping(formula)

    def walk_times(self, formula, args, **kwargs):
        '''translate TIMES node'''
        #pylint: disable=unused-argument
        return self._apply_mapping(formula)

    def walk_pow(self, formula, args, **kwargs):
        '''translate POW node'''
        #pylint: disable=unused-argument
        return self._apply_mapping(formula)

    def walk_minus(self, formula, args, **kwargs):
        '''translate MINUS node'''
        #pylint: disable=unused-argument
        return self._apply_mapping(formula)

    def walk_algebraic_constant(self, formula, args, **kwargs):
        '''translate ALGEBRAIC CONST node'''
        #pylint: disable=unused-argument
        return self._apply_mapping(formula)

    def walk_real_constant(self, formula, args, **kwargs):
        '''translate REAL CONST node'''
        #pylint: disable=unused-argument
        return self._apply_mapping(formula)

    def walk_int_constant(self, formula, args, **kwargs):
        '''translate INT CONST node'''
        #pylint: disable=unused-argument
        return self._apply_mapping(formula)

    def walk_str_constant(self, formula, **kwargs):
        '''translate STR CONST node'''
        #pylint: disable=unused-argument
        return self._apply_mapping(formula)
