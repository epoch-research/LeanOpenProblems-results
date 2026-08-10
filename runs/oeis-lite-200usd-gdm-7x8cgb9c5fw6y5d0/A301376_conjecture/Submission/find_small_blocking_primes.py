import sys
import time
from sympy import isprime

def get_V_all(N2_limit):
    V = {1}
    for s in range(10):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(20):
            val = fs * 4**i
            if val < N2_limit:
                V.add(val)
    return sorted(list(V))

PRIME_LIMIT = 20000
primes_pool = [p for p in range(3, PRIME_LIMIT) if p % 4 == 3 and isprime(p)]
print(f"Number of primes up to {PRIME_LIMIT} with p % 4 == 3: {len(primes_pool)}")

# Let's search N from 1,000,000 to 10,000,000
# Precompute V for the max N we will search (N = 10,000,000 => N^2 = 10^14)
max_N = 10000000
V_max = get_V_all(max_N * max_N)
print(f"Precomputed V_max size: {len(V_max)}")

t0 = time.time()
for N in range(1000000, max_N):
    if N % 100000 == 0:
        print(f"Checked up to N = {N}, time: {time.time() - t0:.2f}s", flush=True)
        
    N2 = N * N
    # Filter precomputed V_max
    V_all = [v for v in V_max if v < N2]
    
    all_blocked = True
    blocking_primes = {}
    for v in V_all:
        diff = N2 - v
        if diff == 0:
            all_blocked = False
            break
            
        found = False
        for p in primes_pool:
            if diff % p == 0:
                if (diff // p) % p != 0:
                    blocking_primes[v] = p
                    found = True
                    break
        if not found:
            all_blocked = False
            break
            
    if all_blocked:
        print(f"\nFOUND SUCCESSFUL N = {N}")
        print(f"N^2 = {N2}")
        print(f"V_all size: {len(V_all)}")
        print(f"blocking_primes = {blocking_primes}")
        print(f"Max blocking prime: {max(blocking_primes.values())}")
        sys.exit(0)

print("Finished search without finding a solution.")
