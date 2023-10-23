from pysmt.walkers import DagWalker
from pysmt.fnode import FNode

from pysmt.shortcuts import And,Or,Iff,Implies,TRUE,FALSE,Not,Ite

class NormalizerWalker(DagWalker):
    '''A walker to normalize smt formulas'''

    def __init__(self, converter, env=None, invalidate_memoization=False):
        DagWalker.__init__(self, env, invalidate_memoization)
        self._converter = converter
        return

    def walk_and(self, formula: FNode, args, **kwargs):
        '''translate AND node'''
        #pylint: disable=unused-argument
        return And(*args)

    def walk_or(self, formula: FNode, args, **kwargs):
        '''translate OR node'''
        #pylint: disable=unused-argument
        return Or(*args)
    
    def walk_not(self, formula: FNode, args, **kwargs):
        '''translate NOT node'''
        #pylint: disable=unused-argument
        return Not(args[0])

    def walk_symbol(self,formula: FNode, args, **kwargs):
        '''translate SYMBOL node'''
        #pylint: disable=unused-argument
        return self._convert(formula)
    
    def walk_bool_constant(self,formula: FNode, args, **kwargs):
        '''translate BOOL const node'''
        #pylint: disable=unused-argument
        value = formula.constant_value()
        if value:
            return TRUE()
        return FALSE()

    def walk_iff(self, formula, args, **kwargs):
        '''translate IFF node'''
        #pylint: disable=unused-argument
        return Iff(args[0],args[1])

    def walk_implies(self, formula, args, **kwargs):
        '''translate IMPLIES node''' # a -> b === (~ a) v b
        #pylint: disable=unused-argument
        return Implies(args[0],args[1])
    
    def walk_ite(self, formula, args, **kwargs):
        '''translate ITE node'''
        #pylint: disable=unused-argument
        return Ite(args[0],args[1],args[2])
    
    def _convert(self,formula):
        msat_term = self._converter.convert(formula)
        return self._converter.back(msat_term)


    def walk_le(self, formula, args, **kwargs):
        '''translate LE node'''
        #pylint: disable=unused-argument
        return self._convert(formula)

    def walk_lt(self, formula, args, **kwargs):
        '''translate LT node'''
        #pylint: disable=unused-argument
        return self._convert(formula)
    
    def walk_equals(self, formula, args, **kwargs):
        '''translate EQUALS node'''
        #pylint: disable=unused-argument
        return self._convert(formula)

    def walk_plus(self, formula, args, **kwargs):
        '''translate PLUS node'''
        #pylint: disable=unused-argument
        return self._convert(formula)

    def walk_times(self, formula, args, **kwargs):
        '''translate TIMES node'''
        #pylint: disable=unused-argument
        return self._convert(formula)

    def walk_pow(self, formula, args, **kwargs):
        '''translate POW node'''
        #pylint: disable=unused-argument
        return self._convert(formula)

    def walk_minus(self, formula, args, **kwargs):
        '''translate MINUS node'''
        #pylint: disable=unused-argument
        return self._convert(formula)

    def walk_algebraic_constant(self, formula, args, **kwargs):
        '''translate ALGEBRAIC CONST node'''
        #pylint: disable=unused-argument
        return self._convert(formula)

    def walk_real_constant(self, formula, args, **kwargs):
        '''translate REAL CONST node'''
        #pylint: disable=unused-argument
        return self._convert(formula)

    def walk_int_constant(self, formula, args, **kwargs):
        '''translate INT CONST node'''
        #pylint: disable=unused-argument
        return self._convert(formula)

    def walk_str_constant(self, formula, **kwargs):
        '''translate STR CONST node'''
        #pylint: disable=unused-argument
        return self._convert(formula)
