import math
import sys
from sympy import factorint

# Precompute allowed residues for sums of two squares modulo small primes
allowed_mod = {}
for p in [3, 7, 11, 19, 23, 31, 43, 47]:
    allowed_mod[p] = set((x*x + y*y) % p for x in range(p) for y in range(p))

def is_sum_of_two_squares_fast(n):
    if n < 0: return False
    if n == 0 or n == 1: return True
    m8 = n % 8
    if m8 in {3, 6, 7}: return False
    for p, allowed in allowed_mod.items():
        if (n % p) not in allowed:
            return False
    # Factor if passes mod filters
    factors = factorint(n)
    for p, exp in factors.items():
        if p % 4 == 3 and exp % 2 != 0:
            return False
    return True

def get_V_all(limit):
    V = {1}
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

print("Starting search...")
sys.stdout.flush()

for N in range(1, 10000000):
    if N % 100000 == 0:
        print(f"Checked up to N = {N}", flush=True)
    N2 = N*N
    V_all = get_V_all(N2)
    any_sol = False
    for v in V_all:
        if is_sum_of_two_squares_fast(N2 - v):
            any_sol = True
            break
    if not any_sol:
        print(f"FOUND COUNTEREXAMPLE! N = {N}")
        print(f"N^2 = {N2}")
        print(f"V_all: {V_all}")
        sys.stdout.flush()
        break
