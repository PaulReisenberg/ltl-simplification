import sys

from tl_simplification.ltl import *
from tl_simplification.utils.int_set import IntegerSet
from tl_simplification.simplification.interval_functions import *
import random
import unittest


class TestSimplifyToBool(unittest.TestCase):

    """
    These Unit Tests test the Simplify Function. Specifically they test the cases in which a formula can be reduced to either true or false. (case 1/2)
    The tests are "fuzzy" tests. This is done because there are many different cases distinctions wether the sets are infinite or not. In each itereration
    random sets and intervals are created. Then, the function is called. We compare the result with the finite case in why we append 200 elements to a set in case
    it is infinite and the only compare the result to the reference set up until this point.
    """

    
    def test_X(self):
        for _ in range(999):
            # 1. Create random sets and a random interval
            I_true_r = get_random_set()
            I_false_r = get_random_set()
            (a,b) = get_random_interval()

            # 2. Apply the function
            I_true, I_false = interval_X(I_true_r, I_false_r, (a,b))

            # 3. Compare with deterministic computation to determine pass/fail
            check = check_X(I_true_r, I_false_r, (a,b), I_true, I_false)
            
            if not check:
                print(f"I_true_r  : {I_true_r}")
                print(f"I_false_r : {I_false_r}")
                print(f"a: {a}, b: {b}")
                print(f"I_true    : {I_true}")
                print(f"I_false   : {I_false}")
                print("------------")

            self.assertTrue(check)


    def test_G(self):
        for _ in range(999):
            # 1. Create random sets and a random interval
            I_true_r = get_random_set()
            I_false_r = get_random_set()
            (a,b) = get_random_interval()

            # 2. Apply the function
            I_true, I_false = interval_G(I_true_r, I_false_r, (a,b))

            # 3. Compare with deterministic computation to determine pass/fail
            check = check_G(I_true_r, I_false_r, (a,b), I_true, I_false)
            
            if not check:
                print(f"I_true_r  : {I_true_r}")
                print(f"I_false_r : {I_false_r}")
                print(f"a: {a}, b: {b}")
                print(f"I_true    : {I_true}")
                print(f"I_false   : {I_false}")
                print("------------")

            self.assertTrue(check)


    def test_F(self):
        for _ in range(999):
            # 1. Create random sets and a random interval
            I_true_r = get_random_set()
            I_false_r = get_random_set()
            (a,b) = get_random_interval()

            # 2. Apply the function
            I_true, I_false = interval_F(I_true_r, I_false_r, (a,b))

            # 3. Compare with deterministic computation to determine pass/fail
            check = check_F(I_true_r, I_false_r, (a,b), I_true, I_false)
            
            if not check:
                print(f"I_true_r  : {I_true_r}")
                print(f"I_false_r : {I_false_r}")
                print(f"a: {a}, b: {b}")
                print(f"I_true    : {I_true}")
                print(f"I_false   : {I_false}")
                print("------------")

            self.assertTrue(check)

        

    def test_U(self):
        for _ in range(999):
            # 1. Create random sets and a random interval
            I_true_r = get_random_set()
            I_false_r = get_random_set()
            I_true_l = get_random_set()
            I_false_l = get_random_set()
            (a,b) = get_random_interval()

            # 2. Apply the function
            I_true, I_false = interval_U(I_true_l, I_false_l, I_true_r, I_false_r, (a,b))

            # 3. Compare with deterministic computation to determine pass/fail
            check_true = check_U_true(I_true_l, I_true_r, (a,b), I_true)
            if not check_true:
                print(f"I_true_l  : {I_true_l}")
                print(f"I_true_r  : {I_true_r}")
                print(f"a: {a}, b: {b}")
                print(f"I_true    : {I_true}")
                print("------------")
                I_true, I_false = interval_U(I_true_l, I_false_l, I_true_r, I_false_r, (a,b))
            

            check_false = check_U_false(I_false_l, I_false_r, (a,b), I_false)
            if not check_false:
                print(f"I_false_l  : {I_false_l}")
                print(f"I_false_r  : {I_false_r}")
                print(f"a: {a}, b: {b}")
                print(f"I_false    : {I_false}")            
                print("------------")
                I_true, I_false = interval_U(I_true_l, I_false_l, I_true_r, I_false_r, (a,b))

            self.assertTrue(check_true and check_false)
                


def check_G(I_true_r, I_false_r, I, I_true, I_false):
    true_r_inf = I_true_r.is_inf()
    false_r_inf = I_false_r.is_inf()
    I_true_r = I_true_r.get_deterministic()
    I_false_r = I_false_r.get_deterministic()
    I_true = I_true.get_deterministic()
    I_false = I_false.get_deterministic()
    
    a = I[0]
    b = I[1]

    if b == None:
        b = 199

    res_I_true = []

    for i in range(0,200):
        is_true = True
        for n in range(a, b+1):
            if not (i+n>199 and true_r_inf) and not i+n in I_true_r:
                is_true = False
                break
        
        if is_true:
            res_I_true.append(i)

    res_I_false = []
    for i in range(0,200):
        is_false = False
        
        for n in range(a,b+1):
            if i+n in I_false_r:
                is_false = True
                break

            if i+n > 199 and false_r_inf:
                is_false = True
                break


        if is_false:
            res_I_false.append(i)
    
    res_I_true = set(res_I_true)
    res_I_false = set(res_I_false)
    
    if res_I_false != I_false:
        print("failed G for I_false:")
        print(res_I_false)
    
    if res_I_true != I_true:
        print("failed G for I_true:")
        print(res_I_true)
        
    return res_I_false == I_false and res_I_true == I_true

def check_X(I_true_r, I_false_r, I, I_true, I_false):
    true_r_inf = I_true_r.is_inf()
    false_r_inf = I_false_r.is_inf()
    I_true_r = I_true_r.get_deterministic()
    I_false_r = I_false_r.get_deterministic()
    I_true = I_true.get_deterministic()
    I_false = I_false.get_deterministic()
    
    a = I[0]
    b = I[1]

    if b == None:
        b = 199

    res_I_true = []

    for i in range(0,200):
        if i+a in I_true_r or (i+a>199 and true_r_inf):
            res_I_true.append(i)
            

    res_I_false = []
    for i in range(0,200):
        if i+a in I_false_r or (i+a>199 and false_r_inf):
            res_I_false.append(i)
    
    res_I_true = set(res_I_true)
    res_I_false = set(res_I_false)
    
    if res_I_false != I_false:
        print("failed X for I_false:")
        print(res_I_false)
    
    if res_I_true != I_true:
        print("failed X for I_true:")
        print(res_I_true)
        
    return res_I_false == I_false and res_I_true == I_true
    
def check_F(I_true_r, I_false_r, I, I_true, I_false):
    true_r_inf = I_true_r.is_inf()
    false_r_inf = I_false_r.is_inf()
    I_true_r = I_true_r.get_deterministic()
    I_false_r = I_false_r.get_deterministic()
    I_true = I_true.get_deterministic()
    I_false = I_false.get_deterministic()
    
    a = I[0]
    b = I[1]

    if b == None:
        b = 199

    res_I_true = []
    for i in range(0,200):
        for n in range(a, b+1):
            if i+n in I_true_r or (i+n>199 and true_r_inf):
                res_I_true.append(i)
                break

    res_I_false = []
    for i in range(0,200):
        is_false = True
        for n in range(a, b+1):
            if not (i+n in I_false_r or (i+n>199 and false_r_inf)):
                is_false = False
                break

        if is_false:
            res_I_false.append(i)
    
    res_I_true = set(res_I_true)
    res_I_false = set(res_I_false)
    
    if res_I_false != I_false:
        print("failed F for I_false:")
        print(res_I_false)
    
    if res_I_true != I_true:
        print("failed F for I_true:")
        print(res_I_true)
        
    return res_I_false == I_false and res_I_true == I_true

def check_U_true(I_true_l,I_true_r, I, I_true):
    true_r_inf = I_true_r.is_inf()
    
    true_l_inf = I_true_l.is_inf()
    
    
    I_true_r = I_true_r.get_deterministic()
    I_true_l = I_true_l.get_deterministic()
    I_true = I_true.get_deterministic()


    a = I[0]
    b = I[1]

    if b == None:
        b = 199

    # True Set
    res_I_true = []
    for t in range(0,200):
        for n in range(0,b+1):
            if n>=a:
                if t+n in I_true_r or (true_r_inf and t+n>199):
                    res_I_true.append(t)
                    break
            if t+n in I_true_l or (true_l_inf and t+n>199):
                continue
            else:
                break
    
    res_I_true = set(res_I_true)
    
    
    
    if res_I_true != I_true:
        print("failed U for I_true:")
        print(res_I_true)
        
    return res_I_true == I_true

def check_U_false(I_false_l, I_false_r, I, I_false):
    
    false_r_inf = I_false_r.is_inf()
    
    false_l_inf = I_false_l.is_inf()
    
    I_false_r = I_false_r.get_deterministic()
    I_false_l = I_false_l.get_deterministic()
    I_false = I_false.get_deterministic()

    a = I[0]
    b = I[1]

    if b == None:
        b = 199


    res_I_false = []
    for t in range(0,200):
        is_false = True
        for n in range(a,b+1):
            if not (t+n in I_false_r or (t+n>199 and false_r_inf)):
                is_false = False

        if is_false:
            res_I_false.append(t)
            continue

        
        for n in range(0,a):
            if (t+n in I_false_l or (t+n>199 and false_l_inf)):
                is_false = True
                break
        
        if is_false:
            res_I_false.append(t)
            continue

        for n in range(a,b+1):
            if t+n in I_false_r or (t+n>199 and false_r_inf):
                if t+n in I_false_l or (t+n>199 and false_l_inf):
                    res_I_false.append(t)
                    break
                else:
                    continue
            else:
                break
        
            
    res_I_false = set(res_I_false)
    
    if res_I_false != I_false:
        print("failed U for I_false:")
        print(f"I_false_res: {IntegerSet(res_I_false, False)}")
        
    

        
    return res_I_false == I_false

def get_random_set():

    l = random.randint(0,60)
    s = []
    for i in range(l):
        if random.randint(0,1) == 1:
            s.append(i)

    s = set(s)
    if random.randint(0,1) == 1:
        int_set = IntegerSet(s, True)
    else:
        int_set = IntegerSet(s, False)

    return int_set

def get_random_interval():

    a = random.randint(0,20)
    if random.randint(0,1) != 1:
        b = a+random.randint(0,20)
    else:
        b = None

    return (a,b)


if "__main__" == __name__:
    unittest.main()
    