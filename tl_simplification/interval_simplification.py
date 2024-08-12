from tl_simplification.simplification.predicate_checker import PredicateChecker
from tl_simplification.ltl import *
from tl_simplification.utils.int_set import IntegerSet, BiDict

# Import subfunctions of the IntervalSimplification algorithm
from tl_simplification.simplification.propagate_interval import propagate_interval
from tl_simplification.simplification.simplify import simplify, simplify_multi

    
def interval_simplification(exp : Expression, I : IntegerSet, pred_check : PredicateChecker):
        
        """
        IntervalSimplification algorithm as explained in my thesis. The knowledge map P is replaced by the PredicateChecker.
        @Params:
        - exp : Expression              : expression to be simplified
        - I : IntegerSet                : a set of trace positions at which the formula should be simplified
        - pred_check : PredicateChecker : Instance of a class that inherits from PredicateChecker
        
        """

        match exp:
            case AtomicProposition(ap):
                # We do not simplify propositions, only predicates
                S = BiDict()
                S.add_exp_in(exp, I)
                return S

            case Predicate(name, terms):
                # A "predicate_check" is performed which is analog to using the knowledge map P in my thesis 
                I_true, I_false = pred_check.check_predicate(name, terms)
                S = BiDict()
                S.add_exp_in(Wahr(), I_true.intersection(I))
                S.add_exp_in(Falsch() ,I_false.intersection(I))
                S.add_exp_in(exp, I.without(I_false.union(I_true)))
                return S

            case Wahr():
                S = BiDict()
                S.add_exp_in(Wahr(),IntegerSet.n0().intersection(I))
                return S
                
            case Falsch():
                S = BiDict()
                S.add_exp_in(Falsch(),IntegerSet.n0().intersection(I))
                return S
            
            case UnaryExpression(op_type, exp):
                # PropagateInterval
                I_r = propagate_interval(I, op_type)

                # IntervalSimplification
                S_r = interval_simplification(exp, I_r, pred_check)

                # Simplify
                S = simplify(op_type, I, S_r)
                
                return S

            case BinaryExpression(op_type, exp_l, exp_r):
                # PropagateInterval
                I_l, I_r = propagate_interval(I, op_type)

                # IntervalSimplification
                S_l = interval_simplification(exp_l, I_l, pred_check)
                S_r = interval_simplification(exp_r, I_r, pred_check)

                # Simplify
                S = simplify(op_type, I, S_r, S_l)
                return S

            case MultiExpression(op_type, expressions):
                # PropagateInterval
                I_sub = propagate_interval(I, op_type)

                # IntervalSimplification
                S_sub = [interval_simplification(exp_sub, I_sub, pred_check) for exp_sub in expressions]

                # Simplify
                S = simplify_multi(op_type, I_sub, S_sub)

                return S


