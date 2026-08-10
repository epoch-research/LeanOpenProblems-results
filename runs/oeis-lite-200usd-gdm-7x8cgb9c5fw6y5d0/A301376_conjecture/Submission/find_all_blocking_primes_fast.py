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
sys.stdout.flush()

# Small primes up to 500,000
print("Generating small primes...", flush=True)
small_primes = []
for p in range(2, 500000):
    if isprime(p):
        small_primes.append(p)
print(f"Generated {len(small_primes)} small primes.", flush=True)

blocking_primes = {}
unblocked = []

start_time = time.time()
for idx, v in enumerate(V_all):
    if idx % 200 == 0:
        print(f"Processed {idx} elements in {time.time() - start_time:.2f}s...", flush=True)
    diff = N2 - v
    
    # Trial division to find a blocking prime or simplify the number
    temp = diff
    found_p = None
    
    for p in small_primes:
        if p * p > temp and temp > 1:
            # The remaining temp is prime!
            if temp % 4 == 3:
                found_p = temp
            break
            
        if temp % p == 0:
            exp = 0
            while temp % p == 0:
                temp //= p
                exp += 1
            if p % 4 == 3 and exp % 2 != 0:
                found_p = p
                break
                
    if found_p is not None:
        blocking_primes[v] = found_p
    else:
        # If we didn't find any small blocking prime, check the cofactor `temp`
        if temp > 1 and isprime(temp) and temp % 4 == 3:
            blocking_primes[v] = temp
        else:
            unblocked.append((v, temp))

print(f"Time taken to check all: {time.time() - start_time:.2f}s")
print(f"Unblocked elements: {len(unblocked)}")
if len(unblocked) == 0:
    print("SUCCESS! All elements are blocked!")
    primes_used = set(blocking_primes.values())
    print(f"Distinct blocking primes used: {len(primes_used)}")
    print(f"Max blocking prime: {max(primes_used)}")
    print(f"Min blocking prime: {min(primes_used)}")
    
    with open("/workspace/leanproject/Submission/success_25digit.py", "w") as f:
        f.write(f"N = {N}\n")
        f.write(f"blocking_primes = {blocking_primes}\n")
else:
    print("Unblocked elements and their cofactors:")
    for v, temp in unblocked[:10]:
        print(f"v = {v}: cofactor = {temp}")
