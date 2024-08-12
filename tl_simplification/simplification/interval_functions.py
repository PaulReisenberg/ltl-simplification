from typing import Tuple
from typeguard import typechecked
from tl_simplification.ltl import *
from tl_simplification.utils.int_set import IntegerSet


"""
This file provides helper functions for the Simplify function in simplify.py. Each function takes as an input two intervals for each subformula 
where this subformula is known to be true /false and retuns the two intervals where the entire formula is true/false.

Referring to my thesis, these functions cover the first two cases by checking in which intervals
the formula can be reduced to true (I_true) and in which intervals can it be reduced to false (I_false)

As the functions get quite complex I have tested them extensively. If any questions come up or you find a mistake here, this is 
my phone number: +49 176 64840164
"""


@typechecked
def interval_And(I_true_l : IntegerSet, I_false_l : IntegerSet, I_true_r : IntegerSet, I_false_r : IntegerSet) -> Tuple[IntegerSet, IntegerSet]:

        I_true = I_true_l.intersection(I_true_r)
        I_false = I_false_l.union(I_false_r)
        return I_true, I_false

@typechecked
def interval_Or(I_true_l : IntegerSet, I_false_l : IntegerSet, I_true_r : IntegerSet, I_false_r : IntegerSet) -> Tuple[IntegerSet, IntegerSet]:
        
        I_true = I_true_l.union(I_true_r)
        I_false = I_false_l.intersection(I_false_r)
        return I_true, I_false

@typechecked
def interval_Imp(I_true_l : IntegerSet, I_false_l : IntegerSet, I_true_r : IntegerSet, I_false_r : IntegerSet) -> Tuple[IntegerSet, IntegerSet]:
        
        I_true = I_false_l.union(I_true_r)
        I_false = I_true_l.intersection(I_false_r)
        return I_true, I_false
    
@typechecked
def interval_Iff(I_true_l : IntegerSet, I_false_l : IntegerSet, I_true_r : IntegerSet, I_false_r : IntegerSet)  -> Tuple[IntegerSet, IntegerSet]:
        
        I_true = (I_true_l.intersection(I_true_r)).union((I_false_l.intersection(I_false_r)))
        I_false = (I_true_l.intersection(I_false_r)).union((I_false_l.intersection(I_true_r)))
        return I_true, I_false
    
@typechecked
def interval_Not(I_true_r : IntegerSet, I_false_r : IntegerSet)  -> Tuple[IntegerSet, IntegerSet]:
    return I_false_r, I_true_r

@typechecked #tested
def interval_G(I_true_r : IntegerSet, I_false_r : IntegerSet, I) -> Tuple[IntegerSet, IntegerSet]:
        a = I[0]
        b = I[1]
        
        # True Set
        if I_true_r.is_empty():
            I_true = IntegerSet([], False)
        
        elif b == None:
            match(I_true_r.is_inf()):
                case True: 
                    I_true = IntegerSet({max(I_true_r.min_inf_start()-a, 0)}, True)
                case False: 
                    I_true = IntegerSet([],False)

        else:
            match(I_true_r.is_inf()):
                case True: 
                    max_val_true_r = max(I_true_r.int_set)
                    I_true = IntegerSet({t for t in range(0,max_val_true_r+1) if all(I_true_r.contains(t+n) for n in range(a, b + 1))}, False)
                    sat_inf = I_true_r.min_inf_start() - a        # state from which formula is always satisfied
                    I_true = I_true.union(IntegerSet({max(sat_inf, 0)}, True))
                case False: 
                    max_val_true_r = max(I_true_r.int_set)
                    I_true = IntegerSet({t for t in range(0,max_val_true_r+1) if all(I_true_r.contains(t+n) for n in range(a, b + 1))}, False)

        
        # False Set
        if I_false_r.is_empty():
            I_false = IntegerSet([], False)
        elif b == None:
            match (I_false_r.is_inf()):
                case True:
                    I_false = IntegerSet({0}, True)
                
                case False:
                    max_val = I_false_r.max()
                    result_set = {t for t in range(0,max(max_val-a+1, 0))}
                    I_false = IntegerSet(result_set, False)

        else:
            match (I_false_r.is_inf()):
                case True:
                    max_val_false_r = I_false_r.min_inf_start()
                    I_false = IntegerSet({t for t in range(0,max_val_false_r+1) if any(I_false_r.contains(t+n) for n in range(a, b + 1))},False)

                    false_inf = I_false_r.min_inf_start() - b      # state from which all states will not satisfy G(phi) because of infinity of I_false_r
                    I_false = I_false.union(IntegerSet({max(0, false_inf)}, True))
                
                case False:
                    max_val_false_r = I_false_r.max()
                    I_false = IntegerSet({t for t in range(0,max_val_false_r+1) if any(I_false_r.contains(t+n) for n in range(a, b + 1))},False)
        
        return I_true, I_false

@typechecked #tested
def interval_X(I_true_r : IntegerSet, I_false_r : IntegerSet, I) -> Tuple[IntegerSet, IntegerSet]:
        a = I[0]      # The first state contained in the time interval
        
        # True Set:
        I_true = I_true_r.addition(-1 * a)
            
        # False Set:
        I_false = I_false_r.addition(-1 * a)
        
        return I_true, I_false

@typechecked #tested
def interval_F(I_true_r : IntegerSet, I_false_r : IntegerSet, I) -> Tuple[IntegerSet, IntegerSet]:
        a = I[0]
        b = I[1]

        #True Set
        if I_true_r.is_empty():
            I_true = IntegerSet([],False)
        elif b == None:
            match I_true_r.is_inf():
                case True:
                    I_true = IntegerSet([0], True)
                case False:
                    I_true = IntegerSet({t for t in range(0, max(I_true_r.int_set) + 1)}, False)
                    I_true = I_true.addition(-1 * a)
        else:
            match I_true_r.is_inf():
                case True:
                    I_true = IntegerSet([t for t in range(0,I_true_r.min_inf_start()+1) if I_true_r.contains_any(t+a,t+b)], True)

                case False:
                    max_true_val = I_true_r.max()
                    fin_true = [t for t in range(0,max_true_val+1) if I_true_r.contains_any(t+a,t+b)]
                    I_true = IntegerSet(fin_true, False)

        # False Set
        if I_false_r.is_empty():
            I_false = IntegerSet([],False)
        elif b == None:
            match I_false_r.is_inf():
                case True:
                    min_false = max(I_false_r.min_inf_start() - a, 0)
                    I_false = IntegerSet({min_false}, True)
                case False:
                    I_false = IntegerSet([],False)
        else:
            match I_false_r.is_inf():
                case True:
                    max_false_val = I_false_r.min_inf_start()
                    fin_false = {t for t in range(0, max_false_val+1) if I_false_r.contains_all(t+a,t+b)}
                    I_false = IntegerSet(fin_false, False)

                    min_inf_start = I_false_r.min_inf_start()
                    I_false = I_false.union(IntegerSet({min_inf_start}, True))
                case False:
                    max_false_val = I_false_r.max()
                    fin_false = {t for t in range(0, max_false_val+1) if I_false_r.contains_all(t+a,t+b)}
                    I_false = IntegerSet(fin_false, False)

        return I_true, I_false

@typechecked #tested
def interval_U(I_true_l : IntegerSet, I_false_l : IntegerSet, I_true_r : IntegerSet, I_false_r : IntegerSet, I):

        a = I[0]
        b = I[1]
        # True Set
        # I_true = {t | ∃n ∈ [a,b] : t+n ∈ I_true_r & ∀n' < n: t+n' ∈ I_true_l}
        if I_true_r.is_empty():
            I_true = IntegerSet([], False)

        elif b == None:
            # I_true = {t | ∃ n>a : t+n ∈ I_true_r & ∀n' < n: t+n' ∈ I_true_l}
            match (I_true_l.is_inf(), I_true_r.is_inf()):
                case (False, False):
                    # I_true_l: finite
                    # I_true_r: finite
                    # n_max = min(I_true_l.max(), I_true_r.max())
                    # {t ∈ [0, n_max] | ∃ n ∈ [a, n_max - t]: t+n ∈ I_true_r & ∀n' < n: t+n' ∈ I_true_l}
                    n_max = I_true_r.max()
                    I_true = IntegerSet(
                        {t for t in range(0, n_max + 1) 
                            if any(I_true_r.contains(t+n) and I_true_l.contains_all(t+0,t+n-1) for n in range(a, a+n_max + 1))}, 
                        False
                    )
                
                case (True, False):
                    # I_true_l: infinite
                    # I_true_r: finite
                    # n_max = I_true_r.max()
                    # {t ∈ [0, n_max] | ∃ n ∈ [a, n_max - t]: t+n ∈ I_true_r & ∀n' < n: t+n' ∈ I_true_l}
                    n_max = I_true_r.max()
                    I_true = IntegerSet(
                        {t for t in range(0, n_max + 1) 
                            if any(I_true_r.contains(t+n) and I_true_l.contains_all(t+0,t+n-1) for n in range(a, a+n_max + 1))}, 
                        False
                    )
                
                case (False, True):
                    # I_true_l: finite
                    # I_true_r: infinit
                    # n_max = I_true_l.max() - a + 1
                    # {t ∈ [0, n_max] | ∃ n ∈ [a, n_max - t + 1]: t+n ∈ I_true_r & ∀n' < n: t+n' ∈ I_true_l}
                    # if a == 0: U I_true_r
                    n_max = max(I_true_l.max(), I_true_r.min_inf_start())
                    I_true = IntegerSet({t for t in range(0,n_max+1) if any(I_true_r.contains(t+n) and I_true_l.contains_all(t, t+n-1) for n in range(a,a+n_max+1))},
                        False
                    )
                    if a == 0:
                        I_true = I_true.union(I_true_r)
                
                case (True, True):
                    # I_true_l: infinite
                    # I_true_r: infinite
                    n_max = max(I_true_l.min_inf_start(), I_true_r.min_inf_start())
                    # {t ∈ [0,n_max] | ∃ n ∈ [a, n_max - t + 1]: t+n ∈ I_true_r & ∀n' < n: t+n' ∈ I_true_l} U {t >= n_max}

                    I_true = IntegerSet(
                        {t for t in range(0,n_max+1) 
                        if any(I_true_r.contains(t+n) and I_true_l.contains_all(t, t+n-1) for n in range(a,n_max + a + 1))},
                        True
                    )

        else:
            match (I_true_l.is_inf(), I_true_r.is_inf()):
                case (False, False):
                    # I_true_l: finite
                    # I_true_r: finite
                    # n_max = min(I_true_l.max(), I_true_r.max())
                    # {t ∈ [0, n_max] | ∃ n ∈ [a, b]: t+n ∈ I_true_r & ∀n' < n: t+n' ∈ I_true_l}
                    n_max = max(I_true_l.max(),I_true_r.max())
                    I_true = IntegerSet(
                        {t for t in range(0, n_max + 1) 
                            if any(I_true_r.contains(t+n) and I_true_l.contains_all(t+0,t+n-1) for n in range(a, b+1))}, 
                        False
                    )
                
                case (True, False):
                    # I_true_l: infinite
                    # I_true_r: finite
                    # n_max = I_true_r.max()
                    # {t ∈ [0, n_max] | ∃ n ∈ [a, b]: t+n ∈ I_true_r & ∀n' < n: t+n' ∈ I_true_l}
                    n_max = I_true_r.max()
                    I_true = IntegerSet(
                        {t for t in range(0, n_max + 1) 
                            if any(I_true_r.contains(t+n) and I_true_l.contains_all(t+0,t+n-1) for n in range(a, b+1))}, 
                        False
                    )
                
                case (False, True):
                    # I_true_l: finite
                    # I_true_r: infinite
                    # n_max = I_true_l.max() - a + 1
                    # {t ∈ [0, n_max] | ∃ n ∈ [a, n_max - t + 1]: t+n ∈ I_true_r & ∀n' < n: t+n' ∈ I_true_l}
                    # if a == 0: U I_true_r
                    n_max = max(I_true_l.max(), I_true_r.min_inf_start())
                    I_true = IntegerSet(
                        {t for t in range(0,n_max+1) 
                        if any(I_true_r.contains(t+n) and I_true_l.contains_all(t, t+n-1) for n in range(a,b+1))},
                        False
                    )
                    if a == 0:
                        I_true = I_true.union(I_true_r)
                
                case (True, True):
                    # I_true_l: infinite
                    # I_true_r: infinite
                    n_max = max(I_true_l.min_inf_start(), I_true_r.min_inf_start())
                    # {t ∈ [0,n_max] | ∃ n ∈ [a, b]: t+n ∈ I_true_r & ∀n' < n: t+n' ∈ I_true_l} U {t >= n_max}
                    I_true = IntegerSet(
                        {t for t in range(0,n_max+1) 
                        if any(I_true_r.contains(t+n) and I_true_l.contains_all(t, t+n-1) for n in range(a,b + 1))},
                        False
                    ).union(IntegerSet({n_max}, True))
                    
        # False Set
        # I_false = {t | ∀ n ∈ [a,b]: t+n ∈ I_false_r   or  ∃n ∈ [a,b] : ( t+n ∈ I_false_l & ∀ n'<= n : t+n' ∈ I_false_r)}      ∃, ∈, ∀,
        
        if b == None:
            match (I_false_l.is_inf(), I_false_r.is_inf()):
                case (False, False):
                    # I_true_l: finite
                    # I_true_r: finite
                    n_max = max(I_false_l.max(), I_false_r.max())
                    # {t ∈ [0,n_max] | ∃n ∈ [a,b] : t+n ∈ I_false_l}
                    i1 = set([])    # empty, as the interval [a,b] is infinite

                    # {t ∈ [0,n_max] | ∃n ∈ [0,a-1] : t+n ∈ I_false_l}
                    i2 = {t for t in range(0, n_max+1) if I_false_l.contains_any(t,t+a-1)}

                    # {t ∈ [0,n_max] | ∃n ∈ [0,n_max] : t+n ∈ I_false_l & ∀ n'∈[a,n]  : t+n' ∈ I_false_r)}
                    i3 = {t for t in range(0,n_max+1) if any(I_false_l.contains(t+n) and I_false_r.contains_all(t+a,t+n) for n in range(a,n_max-t+1))}

                    
                    I_false = IntegerSet(i1.union(i2).union(i3),False)

                case (True, False):
                    # I_true_l: infinite
                    # I_true_r: finite
                    n_max = max(I_false_l.min_inf_start(), I_false_r.max())

                    # {t ∈ [0,n_max] | ∀n ∈ [a,b] : t+n ∈ I_false_r}
                    # empty, as the interval [a,b] is infinite

                    # {t ∈ [0,n_max] | ∃n ∈ [0,a-1] : t+n ∈ I_false_l}
                    i2 = IntegerSet({t for t in range(0, n_max+1) if I_false_l.contains_any(t,t+a-1)}, a > 0)

                    # {t ∈ [0,n_max] | ∃n ∈ [0,n_max] : t+n ∈ I_false_l & ∀ n'∈[a,n]  : t+n' ∈ I_false_r)}
                    i3 = IntegerSet({t for t in range(0,n_max+1) if any(I_false_l.contains(t+n) and I_false_r.contains_all(t+a,t+n) for n in range(a,n_max-t+1))}, False)
                    
                    I_false = i2.union(i3)

                case (False, True):
                    # I_false_l: finite
                    # I_false_r: infinite
                    n_max = max(I_false_l.max(), I_false_r.min_inf_start())

                    # {t ∈ [0,n_max] | ∃n ∈ [a,b] : t+n ∈ I_false_l}
                    i1 = IntegerSet([I_false_r.min_inf_start()-a], True)

                    # {t ∈ [0,n_max] | ∃n ∈ [0,a-1] : t+n ∈ I_false_l}
                    i2 = IntegerSet({t for t in range(0, n_max+1) if I_false_l.contains_any(t,t+a-1)}, False)

                    # {t ∈ [0,n_max] | ∃n ∈ [0,n_max] : t+n ∈ I_false_l & ∀ n'∈[a,n]  : t+n' ∈ I_false_r)}
                    i3 = IntegerSet({t for t in range(0,n_max+1) if any(I_false_l.contains(t+n) and I_false_r.contains_all(t+a,t+n) for n in range(a,n_max+1))}, False)
                    
                    I_false = i1.union(i2).union(i3)

                case (True, True):
                    # I_false_l: infinite
                    # I_false_r: infinite
                    n_max = max(I_false_l.min_inf_start(), I_false_r.min_inf_start())
                    
                    # {t ∈ [0,n_max] | ∃n ∈ [a,b] : t+n ∈ I_false_l}
                    i1 = IntegerSet([I_false_r.min_inf_start()-a], True)

                    # {t ∈ [0,n_max] | ∃n ∈ [0,a-1] : t+n ∈ I_false_l}
                    i2 = IntegerSet({t for t in range(0, n_max+1) if I_false_l.contains_any(t,t+a-1)}, False)

                    # {t ∈ [0,n_max] | ∃n ∈ [0,n_max] : t+n ∈ I_false_l & ∀ n'∈[a,n]  : t+n' ∈ I_false_r)}
                    i3 = IntegerSet({t for t in range(0,n_max+1) if any(I_false_l.contains(t+n) and I_false_r.contains_all(t+a,t+n) for n in range(a,n_max+1))}, False)
                    
                    I_false = i1.union(i2).union(i3)

        else:
            match (I_false_l.is_inf(), I_false_r.is_inf()):
                case (False, False):
                    # I_true_l: finite
                    # I_true_r: finite
                    n_max = max(I_false_l.max(), I_false_r.max())
                    
                    # {t ∈ [0,n_max] | ∀ n ∈ [a,b]: t+n ∈ I_false_r}
                    i1 = {t for t in range(0,n_max+1) if I_false_r.contains_all(t+a,t+b)}

                    # {t ∈ [0,n_max] | ∃n ∈ [0,b] : t+n ∈ I_false_l & ∀ n'∈[a,n]  : t+n' ∈ I_false_r)}
                    i2 = {t for t in range(0,n_max+1) if any(I_false_l.contains(t+n) and I_false_r.contains_all(t+a,t+n) for n in range(0,b+1))}
                    
                    I_false = IntegerSet(i1.union(i2), False)

                case (True, False):
                    # I_true_l: infinite
                    # I_true_r: finite
                    n_max = max(I_false_r.max(), I_false_l.min_inf_start())
                    
                    # {t ∈ [0,n_max] | ∀ n ∈ [a,b]: t+n ∈ I_false_r}
                    i1 = {t for t in range(0,n_max+1) if I_false_r.contains_all(t+a,t+b)}

                    # {t ∈ [0,n_max] | ∃n ∈ [0,b] : t+n ∈ I_false_l & ∀ n'∈[a,n]  : t+n' ∈ I_false_r)}
                    i2 = {t for t in range(0,n_max+1) if any(I_false_l.contains(t+n) and I_false_r.contains_all(t+a,t+n) for n in range(0,b+1))}
                    
                    I_false = IntegerSet(i1.union(i2), a>0)
                    
                case (False, True):
                    # I_true_l: finite
                    # I_true_r: infinite
                    
                    n_max = I_false_r.min_inf_start()
                    
                    # {t ∈ [0,n_max] | ∀ n ∈ [a,b]: t+n ∈ I_false_r}
                    i1 = {t for t in range(0,n_max+1) if I_false_r.contains_all(t+a,t+b)}

                    # {t ∈ [0,n_max] | ∃n ∈ [0,b] : t+n ∈ I_false_l & ∀ n'∈[a,n]  : t+n' ∈ I_false_r)}
                    i2 = {t for t in range(0,n_max+1) if any(I_false_l.contains(t+n) and I_false_r.contains_all(t+a,t+n) for n in range(0,b+1))}
                    
                    I_false = IntegerSet(i1.union(i2), True)

                case (True, True):
                    # I_true_l: infinite
                    # I_true_r: infinite
                    n_max = max(I_false_l.min_inf_start(), I_false_r.min_inf_start())
                    # I_false = {t ∈ [0,n_max] | ∀ n ∈ [a,b]: t+n ∈ I_false_r} U {t ∈ [0,n_max] | ∃n ∈ [a,b] : ( t+n ∈ I_false_l & ∀ n'<= n : t+n' ∈ I_false_r)}
                    
                    # {t ∈ [0,n_max] | ∀ n ∈ [a,b]: t+n ∈ I_false_r}
                    i1 = {t for t in range(0,n_max+1) if I_false_r.contains_all(t+a,t+b)}
                    
                     # {t ∈ [0,n_max] | ∃n ∈ [0,b] : t+n ∈ I_false_l & ∀ n'∈[a,n]  : t+n' ∈ I_false_r)}
                    i2 = {t for t in range(0,n_max+1) if any(I_false_l.contains(t+n) and I_false_r.contains_all(t+a,t+n) for n in range(0,b+1))}


                    I_false = IntegerSet(i1.union(i2),True)

        return I_true, I_false
