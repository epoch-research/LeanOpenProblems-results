import sys
import time
from sympy import isprime

def precompute_V():
    V = {1}
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(160):
            val = fs * 4**i
            V.add(val)
    return sorted(list(V))

all_V_precomputed = precompute_V()

# Fast check if a number is a sum of two squares
# Since we only check numbers up to 10^10, we can use a fast factorizer or prime factorization
from sympy import factorint

def is_sum_of_two_squares_fast(n):
    if n < 0: return False
    if n == 0 or n == 1: return True
    # If n has any prime factor p = 3 mod 4 with odd exponent, return False
    factors = factorint(n)
    for p, exp in factors.items():
        if p % 4 == 3 and exp % 2 != 0:
            return False
    return True

print("Searching N up to 100,000...", flush=True)
start_time = time.time()
found_any = False
for N in range(3, 100000, 2):
    N2 = N * N
    V_all = [v for v in all_V_precomputed if v < N2]
    
    # Check if any v is a sum of two squares
    has_sol = False
    for v in V_all:
        if is_sum_of_two_squares_fast(N2 - v):
            has_sol = True
            break
            
    if not has_sol:
        print(f"\nSUCCESS! FOUND COUNTEREXAMPLE N = {N}")
        print(f"N^2 = {N2}")
        print(f"V_all size = {len(V_all)}")
        found_any = True
        break

if not found_any:
    print(f"No counterexample found under 100,000 in {time.time() - start_time:.2f}s.")
