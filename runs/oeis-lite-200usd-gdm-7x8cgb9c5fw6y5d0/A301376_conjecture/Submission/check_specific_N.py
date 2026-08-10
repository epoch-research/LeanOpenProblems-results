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

N = 1161740213061274220886037
N2 = N * N

# Filter V_all < N2
V_all = [v for v in all_V_precomputed if v < N2]
print(f"N = {N}")
print(f"V_all size: {len(V_all)}")

# Try to cover with primes congruent to 3 mod 4 up to 500,000
print("Generating prime pool...")
prime_pool = [p for p in range(3, 500000) if p % 4 == 3 and isprime(p)]
print(f"Prime pool size: {len(prime_pool)}")
sys.stdout.flush()

unblocked = []
blocking_primes = {}

start_time = time.time()
for idx, v in enumerate(V_all):
    diff = N2 - v
    found_p = None
    for p in prime_pool:
        if diff % p == 0 and diff % (p*p) != 0:
            found_p = p
            break
    if found_p is not None:
        blocking_primes[v] = found_p
    else:
        unblocked.append(v)

print(f"Unblocked elements: {len(unblocked)}")
if len(unblocked) == 0:
    print("SUCCESS! N is a complete counterexample!")
    print(f"Time taken: {time.time() - start_time:.2f}s")
    print(f"Number of distinct blocking primes used: {len(set(blocking_primes.values()))}")
    with open("/workspace/leanproject/Submission/success_specific.py", "w") as f:
        f.write(f"N = {N}\n")
        f.write(f"blocking_primes = {blocking_primes}\n")
else:
    print(f"Unblocked list sample: {unblocked[:20]}")
