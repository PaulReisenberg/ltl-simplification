from tl_simplification.ltl import *
from tl_simplification.utils.int_set import IntegerSet

"""
Implemtation of the PropagateInterval function from my thesis

Given the intervals at which the subformulas can be evaluated this function returns the set of 
trace positions / time steps at which the entire formula can be evaluated during the verification process.
"""

def propagate_interval(I : IntegerSet, op_type):
    match op_type:
        case TempBinOp(op, (a,b)):
            match op:
                case "U":
                    if b == None or I.is_inf():
                        I_l = IntegerSet([I.min()], True)
                    else:
                        I_l = IntegerSet([t for t in range(I.min(), I.max()+b)])
                    
                    if b == None or I.is_inf():
                        I_r = IntegerSet([I.min()+a], True)
                    else:
                        I_r = IntegerSet([t for t in range(I.min()+a, I.max()+b+1)])
                    return I_l, I_r
        
        case TempUnOp(op, (a,b)):
            match op:    
                case "G": 
                    if b == None or I.is_inf():
                        return IntegerSet([I.min()+a], True)
                    else:
                        return IntegerSet.from_interval((I.min() + a, I.max() + b))
                case "F":
                    if b == None or I.is_inf():
                        return IntegerSet([I.min()+a], True)
                    else:
                        return IntegerSet.from_interval((I.min() + a, I.max() + b))
                case "O":
                    if I.is_inf():
                        if b == None:
                            return IntegerSet.n0()
                        else:
                            return IntegerSet([max(0,I.min()-b)], True)
                    else:
                        if b == None:
                            return IntegerSet.from_interval((0, I.max() - a), False)
                        else:
                            return IntegerSet.from_interval((max(0, I.min() - b), I.max() - a), False)
                case "X":
                    return I.addition(a)
                case "P":
                    return I.addition(-1 * a)

        case LogicUnOp(op):
            match op:
                case "not": return I
        
        case LogicBinOp(op):
            return I,I
        
        case LogicMultiOp(op):
            return I
