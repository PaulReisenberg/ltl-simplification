import sys
import unittest
from tl_simplification.ltl import *
from tl_simplification.utils.int_set import IntegerSet
import tl_simplification.ltl as LTL
import random


class TestIntSet(unittest.TestCase):

    def test_fuzzy(self):
        for i in range(999):
            l1 = random.randint(0,60)
            s1 = []
            for i in range(l1):
                if random.randint(0,1) == 1:
                    s1.append(i)
            set1 = set(s1)

            l2 = random.randint(0,60)
            s2 = []
            for i in range(l2):
                if random.randint(0,1) == 1:
                    s2.append(i)
            set2 = set(s2)

            if random.randint(0,1) == 1:
                int_set1 = IntegerSet(set1, True)
            else:
                int_set1 = IntegerSet(set1, False)

            if random.randint(0,1) == 1:
                int_set2 = IntegerSet(set2, True)
            else:
                int_set2 = IntegerSet(set2, False)

            int_result = int_set1.intersection(int_set2)
            
            if not check_intersection_deterministic(int_set1, int_set2, int_result):
                print("failed intersection")
                print(int_set1)
                print(int_set2)
                print(int_result)
                self.fail()


            int_result = int_set1.union(int_set2)
            
            if not check_union_deterministic(int_set1, int_set2, int_result):
                print("failed union")
                print(int_set1)
                print(int_set2)
                print(int_result)
                self.fail()


            if not check_equals_deterministic(int_set1, int_set2, int_set1.equals(int_set2)):
                print("failed equals")
                self.fail()

            int_complement = int_set1.complement()

            if not check_complement_deterministic(int_set1, int_complement):
                print("failed complement")
                print(int_set1)
                print(int_complement)
                self.fail()

            if not check_is_empty_deterministic(int_set1, int_set1.is_empty()):
                print("failed is empty")

            res = int_set1.is_N0()
            if not check_is_n0_deterministic(int_set1, res):
                print(int_set1)
                print(res)
                print("failed is n0")
                self.fail()

            n = random.randint(0,199)
            res = int_set1.contains(n)
            if not check_contains_deterministic(int_set1,n,res):
                print("failed contains")
                self.fail()


            n = random.randint(-10,10)
            res = int_set1.addition(n)
            if not check_addition(int_set1, n, res):
                print("failed addition")
                print(int_set1)
                print(n)
                print(res)
                self.fail()

            a = random.randint(0,60)
            if random.randint(0,1) == 1:
                b = random.randint(0,60)
            else:
                b = None

            cont_any = int_set1.contains_any(a,b)

            if not check_contains_any(int_set1, a,b,cont_any):
                print("contains any failed")
                self.fail()

            cont_all = int_set1.contains_all(a,b)

            if not check_contains_all(int_set1, a,b,cont_all):
                print("contains all failed")
                print(int_set1)
                print(f"a : {a}, b: {b}")
                print(cont_all)
                self.fail()

            if(int_set1.is_inf()):
                n = int_set1.min_inf_start()
                if not check_min_inf_start(int_set1, n):
                    print("failed min inf start")
                    self.fail()



def check_union_deterministic(int_set1 : IntegerSet, int_set2, int_result):
    set1 = int_set1.get_deterministic()
    set2 = int_set2.get_deterministic()
    result = int_result.get_deterministic()

    for x in set1:
        if not x in result:
            return False

    for x in set2:
        if not x in result:
            return False

    for x in result:
        if not x in set1 and not x in set2:
            return False

    return True

def check_intersection_deterministic(int_set1 : IntegerSet, int_set2, int_result):
    set1 = int_set1.get_deterministic()
    set2 = int_set2.get_deterministic()
    result = int_result.get_deterministic()

    for x in set1:
        for y in set2:
            if x == y:
                if not x in result:
                    print("error: " + str(x))
                    return False
    
    for x in result:
        if not x in set1 or not x in set2:
            print("error: " + str(x))
            return False
    return True

def check_equals_deterministic(int_set1: IntegerSet, int_set2: IntegerSet, result : bool):
    det_set1 = int_set1.get_deterministic()
    det_set2 = int_set2.get_deterministic()

    is_equal = det_set1 == det_set2

    return is_equal == result

def check_complement_deterministic(int_set1 : IntegerSet, int_result):
    det_set1 = int_set1.get_deterministic()
    det_result = int_result.get_deterministic()

    for i in range(0, 200):

        if i in det_set1 and i in det_result:
            print("error" + str(i))
            return False

        if not i in det_set1 and not i in det_result:
            print("error" + str(i))
            return False

    return True

def check_is_empty_deterministic(int_set1, result):
    det_set1 = int_set1.get_deterministic()
    return result == (len(det_set1) == 0)

def check_is_n0_deterministic(int_set1, result):
    det_set1 = int_set1.get_deterministic()
    for i in range(200):
        if not i in det_set1:
            return False == result

    return True == result

def check_contains_deterministic(int_set, n, result):
    det_set = int_set.get_deterministic()
    return result == (n in det_set)

def check_addition(int_set, n, int_res):
    det_int = int_set.get_deterministic()
    det_res = int_res.get_deterministic()

    for i in det_int:
            if i > 180:
                continue
            if i+n < 0:
                if i+n in det_res:
                    return False
            if i+n >= 0:
                if not i+n in det_res:
                    return False

    for i in det_res:
            if i > 180:
                continue
            if i-n < 0:
                if i-n in det_int:
                    return False
            if i-n >= 0:
                if not i-n in det_int:
                    return False

    return True       

def check_contains_any(int_set, a, b, res):
    det_set = int_set.get_deterministic()
    
    if b == None:
        b = 199

    for i in range(a,b+1):
        if i in det_set:
            return True == res

    return False == res

def check_contains_all(int_set, a, b, res):
    det_set = int_set.get_deterministic()
    
    if b == None:
        b = 199

    for i in range(a,b+1):
        if not i in det_set:
            return False == res

    return True == res

def check_min_inf_start(int_set, n):
    det_set = int_set.get_deterministic()

    n_max = max(det_set)
    min_inf_start = 199
    for i in range(n_max, -1, -1):
        if not i in det_set:
            break
        else:
            min_inf_start = i
    
    return min_inf_start == n



if "__main__" == __name__:
    unittest.main()