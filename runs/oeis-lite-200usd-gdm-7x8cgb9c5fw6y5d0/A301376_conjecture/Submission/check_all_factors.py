import sys
import math
import time
from sympy import factorint
from sympy.ntheory.modular import crt

def precompute_V():
    V = {1}
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(160):
            val = fs * 4**i
            V.add(val)
    return sorted(list(V))

all_V_precomputed = precompute_V()

moduli = [9, 121, 361, 529, 961]
residues = [1, 2, 41, 120, 225]

n_base, prod = crt(moduli, residues)
n_base = int(n_base)
prod = int(prod)

print(f"Base CRT: N0 = {n_base}, prod = {prod}")
sys.stdout.flush()

for k in range(1, 100):
    N = n_base + k * prod
    if N % 2 == 0:
        continue
    N2 = N * N
    V_all = [v for v in all_V_precomputed if v < N2]
    
    print(f"\nChecking k = {k}, N = {N}, V_all size = {len(V_all)}")
    sys.stdout.flush()
    
    all_blocked = True
    blocking_primes = {}
    
    start_time = time.time()
    for idx, v in enumerate(V_all):
        diff = N2 - v
        factors = factorint(diff)
        
        # Find any prime factor p = 3 mod 4 with odd exponent
        found_p = None
        for p, exp in factors.items():
            if p % 4 == 3 and exp % 2 != 0:
                found_p = p
                break
                
        if found_p is not None:
            blocking_primes[v] = found_p
        else:
            print(f"  v = {v} is NOT blocked! Factors: {factors}")
            all_blocked = False
            break
            
    if all_blocked:
        print(f"\nFOUND TRUE COUNTEREXAMPLE N = {N} at k = {k}!")
        print(f"Time taken to verify: {time.time() - start_time:.2f}s")
        print(f"Blocking primes mapping: {blocking_primes}")
        with open("/workspace/leanproject/Submission/success_factored.py", "w") as f:
            f.write(f"N = {N}\n")
            f.write(f"blocking_primes = {blocking_primes}\n")
        break
