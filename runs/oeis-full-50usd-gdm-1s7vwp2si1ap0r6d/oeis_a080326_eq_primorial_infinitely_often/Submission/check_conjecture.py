import numpy as np
from sympy import primerange, mobius

def count_solutions(max_n):
    # mobius and square_free precomputation
    mu = np.zeros(max_n + 1, dtype=np.int8)
    for i in range(1, max_n + 1):
        mu[i] = mobius(i)
        
    # We will mark which n are NOT solutions.
    # Initially all are potential solutions.
    is_sol = np.ones(max_n + 1, dtype=bool)
    is_sol[0] = False
    
    # Sieve over all primes p <= max_n / 6
    primes = list(primerange(2, max_n // 6 + 1))
    
    print(f"Number of primes to check: {len(primes)}")
    
    for p in primes:
        # Precompute modular inverses modulo p
        # inv[x] = x^-1 mod p
        inv = np.zeros(p, dtype=np.int64)
        for x in range(1, p):
            inv[x] = pow(x, p - 2, p)
            
        curr_sum = 0
        limit = max_n // p
        for k in range(1, limit + 1):
            if mu[k] == 1 and k % p != 0:
                curr_sum = (curr_sum + inv[k % p]) % p
            if k >= 6 and curr_sum == 0:
                # Mark all n in [k*p, (k+1)*p) as False
                start = k * p
                end = min((k + 1) * p, max_n + 1)
                is_sol[start:end] = False
                
    sols = np.where(is_sol)[0]
    print(f"Total solutions up to {max_n}: {len(sols)}")
    if len(sols) > 0:
        print(f"Largest 20 solutions: {sols[-20:]}")
    else:
        print("No solutions found!")

count_solutions(100000)
count_solutions(500000)
count_solutions(1000000)
