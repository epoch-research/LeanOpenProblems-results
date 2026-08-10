import sys
import time

def precompute_V():
    V = {1}
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(160):
            val = fs * 4**i
            V.add(val)
    return sorted(list(V))

all_V = precompute_V()

# We can precompute a set of small primes for fast checking
small_primes = [p for p in prime_range(3, 1000) if p % 4 == 3]

def is_blocked_fast(diff):
    # Quick check with small primes first
    for p in small_primes:
        if diff % p == 0:
            if diff % (p*p) != 0:
                return p
    # If not found, use Sage factor
    factors = factor(diff)
    for p, exp in factors:
        if p % 4 == 3 and exp % 2 != 0:
            return int(p)
    return None

def check_candidate(N):
    N2 = N * N
    V_actual = [v for v in all_V if v < N2]
    
    blocking_primes = {}
    for v in V_actual:
        p = is_blocked_fast(N2 - v)
        if p is None:
            # Not blocked! So N is not a counterexample
            return None
        blocking_primes[v] = p
    return blocking_primes

print("Starting fast sequential search...", flush=True)
start_time = time.time()
found = False

# We will search odd N from 100,000 to 1,500,000
for N in range(100001, 1500000, 2):
    if N % 10000 == 1:
        print(f"Checking N around {N}... time elapsed: {time.time() - start_time:.2f}s", flush=True)
    
    bp = check_candidate(N)
    if bp is not None:
        print(f"\nSUCCESS! Found counterexample N = {N}")
        print(f"N^2 = {N*N}")
        print(f"V_all size = {len([v for v in all_V if v < N*N])}")
        print(f"blocking_primes = {bp}")
        found = True
        
        with open("/workspace/leanproject/Submission/success_sage_found.py", "w") as f:
            f.write(f"N = {N}\n")
            f.write(f"blocking_primes = {bp}\n")
        break

if not found:
    print("Search finished, no counterexample found.")
