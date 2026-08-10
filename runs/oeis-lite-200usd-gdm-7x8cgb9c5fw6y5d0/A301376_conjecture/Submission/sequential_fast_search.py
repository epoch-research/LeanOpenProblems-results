import math
import sys
from sympy import factorint

# Precompute allowed residues for sums of two squares modulo small primes
allowed_mod = {}
for p in [3, 7, 11, 19, 23, 31, 43, 47, 59, 67, 71, 79, 83]:
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

def has_solution_fast(N):
    max_v = int(math.log2(2*N)) + 2
    for v in range(max_v):
        for u in range(v + 1):
            if (2**v - 2**u) % 6 == 0:
                x = (2**v + 2**u) // 2
                y = (2**v - 2**u) // 6
                val = x*x + y*y
                if val <= N*N:
                    k = (u + v) // 2
                    if k <= N:
                        rem = N*N - val
                        if is_sum_of_two_squares_fast(rem):
                            return True
    return False

print("Starting sequential search...")
sys.stdout.flush()

for N in range(1, 10000000):
    if N % 100000 == 0:
        print(f"Checked up to N = {N}", flush=True)
    if not has_solution_fast(N):
        print(f"\nFOUND COUNTEREXAMPLE! N = {N}")
        print(f"N^2 = {N*N}")
        sys.stdout.flush()
        break
else:
    print("Checked up to 10,000,000 and found no counterexample.")
