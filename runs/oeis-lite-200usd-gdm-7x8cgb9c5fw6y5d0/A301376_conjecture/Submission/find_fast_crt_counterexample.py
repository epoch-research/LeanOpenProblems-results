import sys
import math
from sympy.ntheory.modular import crt

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

# Moduli and residues for N mod p^2
moduli = [9, 121, 361, 529, 961]
residues = [1, 2, 41, 120, 225]

n_base, prod = crt(moduli, residues)
n_base = int(n_base)
prod = int(prod)

print(f"Base CRT solved: N0 = {n_base}, prod = {prod}")
sys.stdout.flush()

# The 24 small primes pool
small_primes = [3, 7, 11, 19, 23, 31, 43, 47, 59, 67, 71, 79, 83, 103, 107, 127, 131, 139, 151, 163, 167, 179, 191, 199]

for k in range(1, 1000000):
    if k % 10000 == 0:
        print(f"Checked up to k = {k}...", flush=True)
    N = n_base + k * prod
    if N % 2 == 0:
        continue
    N2 = N * N
    
    # Ensure N < 1.27 * 10^24 for mathematical soundness with s < 40 and i < 160 bounds
    if N >= 1.27 * 10**24:
        print("N exceeded the limit of 1.27 * 10^24!")
        break
        
    V_all = get_V_all(N2)
    
    # Check if every v in V_all is blocked by some prime in small_primes
    all_blocked = True
    blocking_primes = {}
    for v in V_all:
        diff = N2 - v
        found_block = False
        for p in small_primes:
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
        print(f"Blocking primes: {blocking_primes}")
        sys.stdout.flush()
        
        with open("/workspace/leanproject/Submission/success_counterexample.py", "w") as f:
            f.write(f"N = {N}\n")
            f.write(f"blocking_primes = {blocking_primes}\n")
        break
