import sys
import math
from sympy import isprime, factorint

def get_V_all(N2_limit):
    V = {1}
    for s in range(10):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(20):
            val = fs * 4**i
            if val < N2_limit:
                V.add(val)
    return sorted(list(V))

# Precompute allowed sum of squares mod small primes
allowed_mod = {}
for p in [3, 7, 11, 19, 23, 31]:
    allowed_mod[p] = set((x*x + y*y) % p for x in range(p) for y in range(p))

def is_sum_of_two_squares_fast(n):
    if n < 0: return False
    if n == 0 or n == 1: return True
    m8 = n % 8
    if m8 in {3, 6, 7}: return False
    for p, allowed in allowed_mod.items():
        if (n % p) not in allowed:
            return False
    # Factorize
    factors = factorint(n)
    for p, exp in factors.items():
        if p % 4 == 3 and exp % 2 != 0:
            return False
    return True

# We check N from 10,000 to 1,105,300
print("Searching for any counterexample N up to 1,105,300...", flush=True)

V_max = get_V_all(1105300 * 1105300)

for N in range(10000, 1105300):
    if N % 100000 == 0:
        print(f"Checked up to N = {N}", flush=True)
        
    N2 = N * N
    V_all = [v for v in V_max if v < N2]
    
    has_sol = False
    for v in V_all:
        if is_sum_of_two_squares_fast(N2 - v):
            has_sol = True
            break
            
    if not has_sol:
        print(f"\nFOUND MATHEMATICAL COUNTEREXAMPLE N = {N}")
        print(f"N^2 = {N2}")
        sys.exit(0)

print("No mathematical counterexample found under 1,105,300.")
