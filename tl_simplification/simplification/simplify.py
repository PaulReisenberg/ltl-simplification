from typeguard import typechecked
from tl_simplification.ltl import *
from tl_simplification.utils.int_set import IntegerSet, BiDict


from tl_simplification.simplification.propagate_interval import propagate_interval
import tl_simplification.ltl as LTL
from tl_simplification.simplification.interval_functions import *

"""
Implemtation of the Simplify function from my thesis
"""


@typechecked
def simplify(op_type, I : IntegerSet, S_r : BiDict, S_l = None):
        
        match op_type:
            case TempBinOp(op, (a,b)):
                match op:
                    case "U": return simplify_U(I, S_l, S_r,a,b)
                        
            case TempUnOp(op, (a,b)):
                match op:
                    case "G": return simplify_G(I, S_r, a,b)
                    case "F": return simplify_F(I, S_r, a,b)
                    case "X": return simplify_X(I, S_r, a)
                                             
            case LogicBinOp(op):
                match op:
                    case "and": return simplify_AND(I, S_l, S_r)
                    case "or": return simplify_OR(I, S_l, S_r)
                    case "imp": return simplify_IMP(I, S_l, S_r)

            case LogicUnOp(op):
                match op:
                    case "not": return simplify_NOT(I, S_r)

@typechecked
def simplify_multi(op_type, I : IntegerSet, S_sub : List[BiDict]):
        match op_type:
            case LogicMultiOp(op):
                match(op):
                
                    case "conjunction":
                        S = S_sub[0]
                        for i in range(1, len(S_sub)):
                            S = simplify_AND(I, S, S_sub[i])
                        return S

                    case "disjunction":
                        S = S_sub[0]
                        for i in range(1, len(S_sub)):
                            S = simplify_OR(I, S, S_sub[i])
                        return S

@typechecked
def simplify_U(I : IntegerSet, S_l : BiDict, S_r : BiDict, a, b):
        """
        This function is the implementation of the Simplify functino for the Until operator. (Thesis page 21)
        """

        # Case 1 & 2: Formula can be reduced to true or false
        I_true, I_false = interval_U(S_r.get_I(Wahr()), S_r.get_I(Falsch()), S_l.get_I(Wahr()), S_l.get_I(Falsch()), (a,b))
        S = BiDict()
        S.add_exp_in(Wahr(), I_true)
        S.add_exp_in(Falsch(), I_false)
        I = I.without(I_true.union(I_false))

        # Case 3: Formula can not be reduced to true or false

        # J represents the set of all simplifications
        J_l = S_l.get_J()
        J_r = S_r.get_J()
        no_change_start_r = S_r.no_change_start()
        no_change_start_l = S_l.no_change_start()
        no_change_start = max(no_change_start_l, no_change_start_r)

        # We compute the simplification mapping for each trace position / time step specified by I
        for t in I:
            
            # 1. step: We comput the Split function and start the "large disjunction"  (Split([a+t, b+t], S_gamma, S_psi))
            #split(J_l, J_r, [a+t, b+t])
            ivl = [a+t, None]
            if ivl[1] != None:
                ivl[1] = b+t

            omega = IntegerSet.from_interval(ivl)
            splits = IntegerSet.split(J_l, J_r, omega)  

            disjunction = []

            for split in splits:        # split = [x,y]
                x = split[0]
                y = split[1]

                # computing the part before the "∧" ensuring exp1 holds continously 
                S_G = simplify_G(IntegerSet([t],False), S_l,0, x-t-1)
                simp_exp1 = S_G.get_at_timestep(t)

                # S_gamma(x) and S_psi(x)
                exp_l = S_l.get_at_timestep(x)
                exp_r = S_r.get_at_timestep(x)

                
                if exp_l == Wahr():
                    right_bound = None if y == None else y-x
                    simp_exp2 = LTL.eventually(exp_r, (x-t, right_bound))
                else:
                    right_bound = None if y == None else (y-x) 
                    simp_exp2 = LTL.next(LTL.until(exp_l, exp_r, (0,right_bound)),x-t)
                
                if simp_exp1 == Wahr():
                    disjunction.append(simp_exp2)
                else:
                    disjunction.append(LTL._and(simp_exp1, simp_exp2))
                

            
            simp_exp = LTL.disjunction(disjunction)

            if t >= no_change_start:                               # At this point simplified formulas do not change anymore
                rest = IntegerSet([t], True).intersection(I)
                S.add_exp_in(simp_exp, rest)    
                return S                    
            else:
                S.add_exp_at(simp_exp, t)
        
        return S

@typechecked
def simplify_G(I : IntegerSet, S_r : BiDict, a, b):
        """
        This function is the implementation of the Simplify function for the Globally operator. (Thesis page 18)
        """
        I_true, I_false = interval_G(S_r.get_I(Wahr()), S_r.get_I(Falsch()), (a,b))
        S = BiDict()
        S.add_exp_in(Wahr(), I_true)
        S.add_exp_in(Falsch(), I_false)
        
        I = I.without(I_true.union(I_false))

        no_change_start_r = S_r.no_change_start()
        for t in I:
            outer_conjunctions = []
            F = S_r.get_F()
                                
            for phi in F:
                inner_conjunctions = []
                if b == None:
                    timestep_interval = (a+t, None)     # timestep_interval = [a+t,b+t]
                else:
                    timestep_interval = (a+t, b+t)
                                    
                partitions = IntegerSet.partition(S_r.get_I(phi).intersection(IntegerSet.from_interval(timestep_interval)))

                for ivl in partitions:      # ivl = [x,y]
                    new_ivl = ivl.copy()
                    new_ivl[0] -= t
                    if new_ivl[1] != None:
                        new_ivl[1] -= t         # new_ivl = [x-t, b-t]

                    inner_conjunctions.append(LTL.always(phi,new_ivl))         # G_[x-t, b-t] phi

                outer_conjunctions.append(LTL.conjunction(inner_conjunctions))


            simp_exp = LTL.conjunction(outer_conjunctions)

            if t >= no_change_start_r:                               # At this point simplified formulas do not change anymore
                rest = IntegerSet([t], True).intersection(I)
                S.add_exp_in(simp_exp, rest)    
                return S                    
            else:
                S.add_exp_at(simp_exp, t)
                            
        return S

@typechecked
def simplify_F(I : IntegerSet, S_r : BiDict, a, b):
        """
        This function is the implementation of the Simplify function for the eventually operator. (Thesis page 20)
        """
        I_true, I_false = interval_F(S_r.get_I(Wahr()), S_r.get_I(Falsch()), (a,b))
        S = BiDict()
        S.add_exp_in(Wahr(), I_true)
        S.add_exp_in(Falsch(), I_false)
        
        I = I.without(I_true.union(I_false))

        no_change_start_r = S_r.no_change_start()
        for t in I:
            outer_disjunctions = []
            F = S_r.get_F()
                                
            for phi in F:
                inner_disjunctions = []
                if b == None:
                    timestep_interval = (a+t, None)     # timestep_interval = [a+t,b+t]
                else:
                    timestep_interval = (a+t, b+t)
                                    
                partitions = IntegerSet.partition(S_r.get_I(phi).intersection(IntegerSet.from_interval(timestep_interval)))

                for ivl in partitions:      # ivl = [x,y]
                    new_ivl = ivl.copy()
                    new_ivl[0] -= t
                    if new_ivl[1] != None:
                        new_ivl[1] -= t         # new_ivl = [x-t, b-t]

                    inner_disjunctions.append(LTL.eventually(phi,new_ivl))         # F_[x-t, b-t] phi

                if len(inner_disjunctions) == 0:
                    continue
                outer_disjunctions.append(LTL.disjunction(inner_disjunctions))

            if len(outer_disjunctions) == 0:
                continue
            
            simp_exp = LTL.disjunction(outer_disjunctions)

            if t >= no_change_start_r:                               # At this point simplified formulas do not change anymore
                rest = IntegerSet([t], True).intersection(I)
                S.add_exp_in(simp_exp, rest)    
                return S                        
            else:
                S.add_exp_at(simp_exp, t)
                            
        return S

@typechecked
def simplify_X(I : IntegerSet, S_r : BiDict, a):
        """
        This function is the implementation of the Simplify function for the Next operator. (Thesis page 17)
        """
        I_true, I_false = interval_X(S_r.get_I(Wahr()), S_r.get_I(Falsch()), (a,None))
        S = BiDict()
        S.add_exp_in(Wahr(), I_true)
        S.add_exp_in(Falsch(), I_false)
        
        I = I.without(I_true.union(I_false))
        
        no_change_start_r = S_r.no_change_start()
        for t in I:
            
            simp_exp = LTL.next(S_r.get_at_timestep(t+a), a)

            if t >= no_change_start_r:                               # At this point simplified formulas do not change anymore
                rest = IntegerSet([t], True).intersection(I)
                S.add_exp_in(simp_exp, rest)    
                return S                        
            else:
                S.add_exp_at(simp_exp, t)
                            
        return S

@typechecked
def simplify_AND(I : IntegerSet, S_l : BiDict, S_r : BiDict):
        """
        This function is the implementation of the Simplify function for the AND operator. (Thesis page 17)
        """
        I_true, I_false = interval_And(S_r.get_I(Wahr()), S_r.get_I(Falsch()), S_l.get_I(Wahr()), S_l.get_I(Falsch()))
        S = BiDict()
        S.add_exp_in(Wahr(), I_true)
        S.add_exp_in(Falsch(), I_false)
        I = I.without(I_true.union(I_false))

        no_change_start_r = S_r.no_change_start()
        no_change_start_l = S_l.no_change_start()
        no_change_start = max(no_change_start_l, no_change_start_r)
        for t in I:
            exp_l = S_l.get_at_timestep(t)
            exp_r = S_r.get_at_timestep(t)

            simp_exp = LTL._and(exp_l, exp_r)
            if exp_l == Wahr():
                simp_exp = exp_r
            elif exp_r == Wahr():
                simp_exp = exp_l


            if t >= no_change_start:                               # At this point simplified formulas do not change anymore
                rest = IntegerSet([t], True).intersection(I)
                S.add_exp_in(simp_exp, rest)    
                break                  
            else:
                S.add_exp_at(simp_exp, t)
                        
        return S

@typechecked
def simplify_OR(I : IntegerSet, S_l : BiDict, S_r : BiDict):
        """
        This function is the implementation of the Simplify function for the OR operator. 
        """
        I_true, I_false = interval_Or(S_r.get_I(Wahr()), S_r.get_I(Falsch()), S_l.get_I(Wahr()), S_l.get_I(Falsch()))
        S = BiDict()
        S.add_exp_in(Wahr(), I_true)
        S.add_exp_in(Falsch(), I_false)
        I = I.without(I_true.union(I_false))

        no_change_start_r = S_r.no_change_start()
        no_change_start_l = S_l.no_change_start()
        no_change_start = max(no_change_start_l, no_change_start_r)
        for t in I:
            exp_l = S_l.get_at_timestep(t)
            exp_r = S_r.get_at_timestep(t)

            simp_exp = LTL._or(exp_l, exp_r)
            if exp_l == Falsch():
                simp_exp = exp_r
            elif exp_r == Falsch():
                simp_exp = exp_l


            if t >= no_change_start:                               # At this point simplified formulas do not change anymore
                rest = IntegerSet([t], True).intersection(I)
                S.add_exp_in(simp_exp, rest)    
                break                  
            else:
                S.add_exp_at(simp_exp, t)
                        
        return S

@typechecked
def simplify_IMP(I : IntegerSet, S_l : BiDict, S_r : BiDict):
        """
        This function is the implementation of the Simplify function for the IMPLICATION operator.
        """
        S_not_l = simplify_NOT(I, S_l)
        return simplify_OR(I, S_not_l,S_r)

@typechecked
def simplify_NOT(I : IntegerSet, S_r : BiDict):
        """
        This function is the implementation of the Simplify function for the OR operator. (Thesis page 16)
        """
        S = BiDict()
        for exp in S_r.expressions():
            interval = S_r.get_I(exp)
            if exp == Wahr():
                S.add_exp_in(Falsch(), interval)
            elif exp == Falsch():
                S.add_exp_in(Wahr(), interval)
            else:
                S.add_exp_in(UnaryExpression(LogicUnOp("not"), exp), interval)
        return S