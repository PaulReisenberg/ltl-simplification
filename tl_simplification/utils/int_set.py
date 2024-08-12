from typing import Set, List
from typeguard import typechecked

from tl_simplification.ltl import *

class IntegerSet():
    """
    This data structure is used to store infinite sets of integers >= 0.    
    """

    @typechecked
    def __init__(self, int_set, to_inf : bool = False):
        # int_set = {} and to_inf = 1 will be interpreted as N0 and int_set will be replaced by {0} upon initialization
        if isinstance(int_set, List):
            self.int_set = set(int_set)
            self.to_inf = to_inf
        elif isinstance(int_set, Set):
            self.int_set = int_set
            self.to_inf = to_inf
        else:
            raise ValueError(f"IntegerSet init only accepts lists or sets. {type(int_set)} not allowed")

        if to_inf and len(int_set) == 0:
            self.int_set = set([0])

    def __str__(self):
        if self.is_empty():
            return "."
        string = ""
        
        for i in range(0,max(self.int_set)+1):
            if self.contains(i):
                string += str(i) + ","
            else:
                string += " "*len(str(i)) + ","
        
        if self.is_inf():
            for i in range(max(self.int_set)+1, max(self.int_set) +10):
                string += str(i) + ","

            string += "...."
        return string

    def get_deterministic(self):
        """
        This function is only used for testing purposes and returns a deterministic representation of the IntegerSet. 
        """

        if not self.is_inf():
            return self.int_set
        else:
            return self.int_set.union({i for i in range(max(self.int_set)+1, 200)})

    def pretty(self):
        if len(self.int_set) == 0:
            return ""
        string = ""
        for i in range(0,max(self.int_set)+1):
            if i in self.int_set:
                string += str(i)+","
            else:
                string +=(" "* len(str(i))) + ","
        
        if self.to_inf:
            for i in range(max(self.int_set), max(self.int_set) +10):
                string += str(i) + ","
            string += "...."

        return string 

    @typechecked #tested
    def contains(self, n : int):
        if self.is_inf():
            return n > max(self.int_set) or n in self.int_set
        else:
            return n in self.int_set

    @typechecked #tested
    def equals(self, int_set2 : 'IntegerSet') -> bool:
                
        match (self.is_inf(), int_set2.is_inf()):
            case (True, True):
                max_inf_start = max(self.min_inf_start(), int_set2.min_inf_start())
                return all(self.contains(i) == int_set2.contains(i) for i in range(0,max_inf_start))
            case (False, True):
                return False
            case (True, False):
                return False
            case (False, False):
                return self.int_set == int_set2.int_set
                
    @typechecked #tested
    def union(self, set2: 'IntegerSet'):
        
        match (self.is_inf(), set2.is_inf()):
            case (False, False): return IntegerSet(self.int_set.union(set2.int_set), False)
            case (True, False): return IntegerSet([i for i in range(0,self.min_inf_start()+1) if self.contains(i) or set2.contains(i)], True)
            case (False, True): return IntegerSet([i for i in range(0,set2.min_inf_start()+1) if self.contains(i) or set2.contains(i)], True)
            case (True, True): return IntegerSet([i for i in range(0,max(self.min_inf_start(), set2.min_inf_start()) + 1) if self.contains(i) or set2.contains(i)], True)
                
    @typechecked #tested
    def intersection(self, set2 : 'IntegerSet'):
        
        if self.is_empty() or set2.is_empty():
            return IntegerSet([], False)
        

        match(self.is_inf(), set2.is_inf()):
            case (False, False): return IntegerSet(self.int_set.intersection(set2.int_set), False)
            case (True, False): return IntegerSet({i for i in set2.int_set if self.contains(i)}, False)
            case (False, True): return IntegerSet({i for i in self.int_set if set2.contains(i)}, False)
            case (True, True): return IntegerSet([i for i in range(0,max(self.min_inf_start(), set2.min_inf_start())+2) if set2.contains(i) and self.contains(i)], True)

    @typechecked #tested
    def complement(self) -> 'IntegerSet':
        
        if len(self.int_set) == 0:
            return IntegerSet({0}, True)

        if self.is_inf():
            n_max = self.min_inf_start()
            return IntegerSet({i for i in range(0,n_max) if not self.contains(i)},False)
        else:
            n_max = self.max()
            return IntegerSet({i for i in range(0,n_max+2) if not self.contains(i)},True)

    @typechecked #tested
    def is_empty(self) -> bool:
        return len(self.int_set) == 0

    @typechecked #tested
    def is_N0(self) -> bool:
        if (not 0 in self.int_set) or (not self.to_inf):
            return False

        m = max(self.int_set)
        
        for i in range(1,m):
            if i not in self.int_set:
                return False

        return True

    @typechecked #tested
    def addition(self, n : int):
        """
        adds n to every element in the set. Additions that result in an integer < 0 will be ignored
        """

        result_set = {x+n for x in self.int_set if x+n >= 0}
        return IntegerSet(result_set, self.to_inf)

    @typechecked #checked
    def add(self, n : int):
        if not self.to_inf:
            self.int_set.add(n)
        else:
            if n < max(self.int_set):
                self.int_set.add(n)

    @typechecked
    def is_inf(self):
        return self.to_inf

    @typechecked #tested
    def min_inf_start(self):
        # Function returns min {i in I | for all n > i : n in I}
        assert self.to_inf

        min = max(self.int_set)
        for i in range(max(self.int_set)-1, -1,-1):     # range max-1,....,0
            if i in self.int_set:
                min = i
            else:
                return min
        return min

    @typechecked #tested
    def min_complete_to_max_start(self):
        
        min = self.max()
        for i in range(max(self.int_set)-1, -1,-1):     # range max-1,....,0
            if i in self.int_set:
                min = i
            else:
                return min
        return min 

    @typechecked #ok
    def min(self):
        assert not self.is_empty()
        return min(self.int_set)

    @typechecked #ok
    def max(self):
        assert not self.is_inf()
        if self.is_empty():
            return -1
        else:
            return max(self.int_set)

    @typechecked #tested
    def contains_any(self, a:int, b=None):
        
        if self.is_empty():
            return False

        if b != None:                   # Bounded interval
            return any(self.contains(i) for i in range(a,b+1))
        
        else:
            if self.is_inf():           # [a,b] and I not bouned -> True
                return True
            else:
                return any(self.contains(i) for i in range(a, self.max()+1))

    @typechecked #tested       
    def contains_all(self, a:int, b=None):
        
        if b != None:                   # bounded interval
            if b < a:
                return True
            return all(self.contains(i) for i in range(a,b+1))
        
        else:
            if self.is_inf():
                min_inf_start = self.min_inf_start()
                return min_inf_start <= a
            else:
                return False

    #ok
    def empty():
        return IntegerSet([], False)
    
    #ok
    def n0():
        return IntegerSet([0], True)

    @typechecked
    def partition(self) -> List[List[int]]:
        # Partition the IntegerSet into contiguous intervals. Used to implement the Split function with one input simplification

        if self.is_inf():
            n_max = self.min_inf_start()
            intervals = []

            recording = False
            for i in range(0,n_max+1):
                if self.contains(i):
                    if not recording:
                        intervals.append([i])
                        recording = True
                else:
                    if recording:
                        intervals[-1].append(i-1)
                        recording = False
            if recording:
                intervals[-1].append(None)

        else:
            n_max = self.max() 
            intervals = []

            recording = False
            for i in range(0,n_max+1):
                if self.contains(i):
                    if not recording:
                        intervals.append([i])
                        recording = True
                else:
                    if recording:
                        
                        intervals[-1].append(i-1)
                        recording = False
            if recording:
                intervals[-1].append(n_max)

        return intervals

    @typechecked
    def split(A : List['IntegerSet'], B : List['IntegerSet'], omega : 'IntegerSet'):
        # Split function with two input simplification from my thesis

        Intervals_a = []
        for a in A:
            if not a.is_empty():
                Intervals_a += a.partition()

        Intervals_b = []
        for b in B:
            if not b.is_empty():
                Intervals_b += b.partition()
        
        result = []
        print(Intervals_a)
        print(Intervals_b)
        for I_a in Intervals_a:
            for I_b in Intervals_b:
                a = IntegerSet.from_interval(I_a)
                b = IntegerSet.from_interval(I_b)

                x = a.intersection(b).intersection(omega)
                if not x.is_empty():
                    if x.is_inf():
                        result.append([x.min(), None])
                    else:
                        result.append([x.min(), x.max()])
        return result

    @typechecked
    def without(self, set2 : 'IntegerSet') -> 'IntegerSet':
        # A/B = a intersection (not b)
        set3 = set2.complement()
        return self.intersection(set3)

    def from_interval(I) -> 'IntegerSet':
        
        if I[1] == None:
            return IntegerSet([I[0]], True)
        else:
            return IntegerSet({i for i in range(I[0], I[1]+1)}, False)

    @typechecked
    def without(self, set2 : 'IntegerSet', ) -> 'IntegerSet':
        return self.intersection(set2.complement())

    def __iter__(self):
        if self.is_empty():
            self.index = None
        else:
            self.index = -1
        return self

    def __next__(self):
        if self.index == None:
            raise StopIteration()
        if self.index < 0:
            self.index = self.min()
            return self.index
        if self.is_inf():
            if self.index >= self.min_inf_start():
                self.index += 1
                return self.index
            else:
                for t in range(self.index+1, self.min_inf_start()+1):
                    if self.contains(t):
                        self.index = t
                        return t
        else:
            if self.index > self.max():
                raise StopIteration()
            else:
                for t in range(self.index+1, self.max()+1):
                    if self.contains(t):
                        self.index = t
                        return t
        
        raise StopIteration()
                


class BiDict:
    """
    This data Structure is used to implement the simplification mapping S.
    It is a dict where each value is a key and vica verca
    """

    def __init__(self):
        self.key_to_value = {}
        self.value_to_key = {}

    def set(self, key, value):
        self.key_to_value[key] = value
        self.value_to_key[value] = key

    def get_I(self, exp):
        
        I = self.key_to_value.get(exp)
        if I == None:
            return IntegerSet.empty()
        return I

    def get_Exp(self, I):
        return self.value_to_key.get(I)

    def intervals(self):
        return list(self.key_to_value.values())

    def expressions(self):
        assert set(self.key_to_value.keys()) == set(self.value_to_key.values())
        return list(self.key_to_value.keys())

    def get_F(self):
        exps = self.expressions()
        exps.remove(Falsch())
        exps.remove(Wahr())
        return exps

    def get_J(self):
        # J represents the set of all simplifications
        return list(self.key_to_value.values())

    def contains_exp(self, exp):
        return exp in self.expressions()


    def add_exp_at(self, exp, timestep):

        if exp in self.key_to_value.keys():
            old_interval = self.key_to_value[exp]
            del self.value_to_key[old_interval]
            self.key_to_value[exp] = old_interval.union(IntegerSet([timestep], False))
            self.value_to_key[self.key_to_value[exp]] = exp

        else:
            self.set(exp, IntegerSet([timestep], False))




    def add_exp_in(self, exp, I):
        if exp in self.key_to_value.keys():
            old_interval = self.key_to_value[exp]
            del self.value_to_key[old_interval]

            self.key_to_value[exp] = old_interval.union(I)
            self.value_to_key[self.key_to_value[exp]] = exp
        else:
            self.set(exp, I)


    def get_at_timestep(self, timestep):
        for invl in self.intervals():
            if invl.contains(timestep):
                return self.value_to_key[invl]

    def print(self):
        for intv in self.intervals():
            print(str(intv) + "->" + str(self.get_Exp(intv)))

        for exp in self.expressions():
            print(str(exp) + "->" + str(self.get_I(exp)))


    def no_change_start(self):
        # returns the minimum value from which the formula does not change
        intervals = self.intervals()
        start = -1
        for I in intervals:
            if I.is_inf():
                return I.min_inf_start()
            elif not I.is_empty():
                if I.min_complete_to_max_start() > start:
                    start = I.min_complete_to_max_start()
        
        return start
