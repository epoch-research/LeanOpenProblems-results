import numpy as np
from sympy import primerange, mobius
import time

def count_solutions(max_n):
    t0 = time.time()
    # Precompute mobius
    mu = np.zeros(max_n + 1, dtype=np.int8)
    for i in range(1, max_n + 1):
        mu[i] = mobius(i)
        
    is_sol = np.ones(max_n + 1, dtype=bool)
    is_sol[0] = False
    
    primes = list(primerange(2, max_n // 6 + 1))
    
    for p in primes:
        # Precompute mod p inverses
        inv = np.zeros(p, dtype=np.int64)
        # Using pow(x, p-2, p)
        # For numpy speed, we can do it with a loop or list comprehension
        inv_list = [pow(x, p - 2, p) for x in range(p)]
        inv = np.array(inv_list, dtype=np.int64)
            
        curr_sum = 0
        limit = max_n // p
        
        # We can extract the mu values for k % p != 0
        # But a simple loop over k is also fast
        for k in range(1, limit + 1):
            if mu[k] == 1 and k % p != 0:
                curr_sum = (curr_sum + inv_list[k % p]) % p
            if k >= 6 and curr_sum == 0:
                start = k * p
                end = min((k + 1) * p, max_n + 1)
                is_sol[start:end] = False
                
    sols = np.where(is_sol)[0]
    t1 = time.time()
    print(f"Total solutions up to {max_n}: {len(sols)} in {t1-t0:.2f} seconds")
    print(f"Largest 20 solutions: {sols[-20:]}")

count_solutions(300000)
count_solutions(1000000)
