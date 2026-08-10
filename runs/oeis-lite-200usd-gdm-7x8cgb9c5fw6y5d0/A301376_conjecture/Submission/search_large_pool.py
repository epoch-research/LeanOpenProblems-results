import sys
import math
from sympy import isprime
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
        
    V_all = get_V_all(N2)
    
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
