import sys
import math
from sympy import isprime, factorint
from sympy.ntheory.modular import crt

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

moduli = [9, 121, 361, 529, 961]
residues = [1, 2, 41, 120, 225]

n_base, prod = crt(moduli, residues)
n_base = int(n_base)
prod = int(prod)

print(f"Base CRT solved: N0 = {n_base}, prod = {prod}")
sys.stdout.flush()

# We start searching for N = n_base + k * prod
# Let's search k up to 50000
for k in range(1, 50000):
    if k % 1000 == 0:
        print(f"Checking k = {k}...", flush=True)
    N = n_base + k * prod
    if N % 2 == 0:
        continue
        
    N2 = N * N
    V_all = get_V_all(N2)
    any_sol = False
    for v in V_all:
        if is_sum_of_two_squares_fast(N2 - v):
            any_sol = True
            break
    if not any_sol:
        print(f"\nFOUND TRUE COUNTEREXAMPLE N = {N}")
        print(f"N^2 = {N2}")
        print(f"k = {k}")
        sys.stdout.flush()
        
        # Find blocking primes
        blocking_primes = {}
        all_primes_pool = [p for p in range(3, 10000) if isprime(p) and p % 4 == 3]
        all_covered = True
        for v in V_all:
            diff = N2 - v
            found_prime = -1
            for p in [3, 7, 11, 19, 23, 31, 43, 47] + all_primes_pool:
                if diff % p == 0 and diff % (p**2) != 0:
                    found_prime = p
                    break
            if found_prime != -1:
                blocking_primes[v] = found_prime
            else:
                print(f"Failed to find blocking prime for v = {v}!")
                all_covered = False
                break
        if all_covered:
            print("SUCCESS! All elements blocked!")
            with open("/workspace/leanproject/Submission/success_counterexample.py", "w") as f:
                f.write(f"N = {N}\n")
                f.write(f"blocking_primes = {blocking_primes}\n")
            break
