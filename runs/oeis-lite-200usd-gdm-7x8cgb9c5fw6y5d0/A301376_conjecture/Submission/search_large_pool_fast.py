import sys
import math
from sympy import isprime
from sympy.ntheory.modular import crt

# Precompute ALL possible v values up to the absolute mathematical limit
def precompute_V():
    V = {1}
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(160):
            val = fs * 4**i
            V.add(val)
    return sorted(list(V))

all_V_precomputed = precompute_V()
print(f"Precomputed {len(all_V_precomputed)} possible v values in total.")

# Moduli and residues for N mod p^2
moduli = [9, 121, 361, 529, 961]
residues = [1, 2, 41, 120, 225]

n_base, prod = crt(moduli, residues)
n_base = int(n_base)
prod = int(prod)

print(f"Base CRT solved: N0 = {n_base}, prod = {prod}")
sys.stdout.flush()

# Large primes pool: all primes congruent to 3 mod 4 up to 5000
prime_pool = [p for p in range(3, 5000) if isprime(p) and p % 4 == 3]
print(f"Prime pool size: {len(prime_pool)}")

for k in range(1, 10000000):
    if k % 10000 == 0:
        print(f"Checked up to k = {k}...", flush=True)
    N = n_base + k * prod
    if N % 2 == 0:
        continue
    N2 = N * N
    
    # Ensure N < 1.27 * 10^24
    if N >= 1.27 * 10**24:
        print("N exceeded the limit of 1.27 * 10^24!")
        break
        
    # Get V_all for N^2 by just filtering/slicing our precomputed list
    # Since all_V_precomputed is sorted, we can binary search or just linear scan (very fast since size < 2000)
    V_all = []
    for v in all_V_precomputed:
        if v >= N2:
            break
        V_all.append(v)
    
    all_blocked = True
    blocking_primes = {}
    for v in V_all:
        diff = N2 - v
        found_block = False
        for p in prime_pool:
            if diff % p == 0 and diff % (p*p) != 0:
                blocking_primes[v] = p
                found_block = True
                break
        if not found_block:
            all_blocked = False
            break
            
    if all_blocked:
        print(f"\nSUCCESS! FOUND TRUE COUNTEREXAMPLE N = {N}")
        print(f"N^2 = {N2}")
        print(f"k = {k}")
        print(f"V_all size = {len(V_all)}")
        print(f"Number of distinct blocking primes used: {len(set(blocking_primes.values()))}")
        sys.stdout.flush()
        
        with open("/workspace/leanproject/Submission/success_large_pool.py", "w") as f:
            f.write(f"N = {N}\n")
            f.write(f"blocking_primes = {blocking_primes}\n")
        break
