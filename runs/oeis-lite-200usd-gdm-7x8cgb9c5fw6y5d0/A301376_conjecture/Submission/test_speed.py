import sys
import time
from sympy import isprime

def get_V_all(N2):
    V = {1}
    for s in range(10):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(20):
            val = fs * 4**i
            if val < N2:
                V.add(val)
    return sorted(list(V))

print("Generating primes...", flush=True)
primes_3mod4_limit = [p for p in range(3, 20000) if p % 4 == 3 and isprime(p)]
print(f"Primes pool size: {len(primes_3mod4_limit)}", flush=True)

# Precompute V_all up to (10^6)^2 = 10^12
print("Precomputing V_all...", flush=True)
V_max = get_V_all(10**12)
print(f"Precomputed V_max size: {len(V_max)}", flush=True)

t0 = time.time()
for N in range(10000, 1000000):
    if N % 50000 == 0:
        print(f"Checked up to N = {N}, time: {time.time() - t0:.2f}s", flush=True)
        
    N2 = N * N
    # Filter precomputed V_max
    V_all = [v for v in V_max if v < N2]
    
    all_blocked_by_small = True
    blocking_primes = {}
    for v in V_all:
        diff = N2 - v
        if diff == 0:
            all_blocked_by_small = False
            break
            
        found = False
        for p in primes_3mod4_limit:
            if p * p > diff:
                break
            if diff % p == 0 and diff % (p*p) != 0:
                blocking_primes[v] = p
                found = True
                break
        if not found:
            all_blocked_by_small = False
            break
            
    if all_blocked_by_small:
        print(f"\nFOUND EASY COUNTEREXAMPLE N = {N}", flush=True)
        print(f"N^2 = {N2}", flush=True)
        print(f"V_all size: {len(V_all)}", flush=True)
        print(f"blocking_primes = {blocking_primes}", flush=True)
        sys.exit(0)
