import sys
import math
from sympy import isprime

def get_V_all(limit):
    V = {1}
    # We can use large ranges because limit is small
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        if fs >= limit:
            break
        for i in range(160):
            val = fs * 4**i
            if val >= limit:
                break
            V.add(val)
    return sorted(list(V))

# Primes pool congruent to 3 mod 4
primes_pool = [p for p in range(3, 1000) if isprime(p) and p % 4 == 3]

# We will search for N starting from 1
for N in range(1, 10000000):
    if N % 10000 == 0:
        print(f"Checking N up to {N}...", flush=True)
        
    N2 = N * N
    V_all = get_V_all(N2)
    
    # We want to see if for every v in V_all, there exists some p in primes_pool
    # such that p | (N2 - v) and p^2 does not divide (N2 - v)
    all_blocked = True
    used_primes = set()
    
    for v in V_all:
        blocked = False
        for p in primes_pool:
            diff = N2 - v
            if diff % p == 0 and diff % (p**2) != 0:
                blocked = True
                used_primes.add(p)
                break
        if not blocked:
            all_blocked = False
            break
            
    if all_blocked:
        print(f"\nFOUND TRUE COUNTEREXAMPLE N = {N}")
        print(f"N^2 = {N2}")
        print(f"V_all size: {len(V_all)}")
        print(f"V_all: {V_all}")
        print(f"Used primes: {sorted(list(used_primes))}")
        # Print the residues mod p^2 for each used prime
        res_dict = {}
        for p in used_primes:
            res_dict[p] = N % (p**2)
        print(f"Residues mod p^2: {res_dict}")
        break
