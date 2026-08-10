import sys
import math
from sympy import isprime, factorint
from sympy.ntheory.modular import crt

allowed_mod = {}
for p in [3, 7, 11, 19, 23, 31, 43, 47]:
    allowed_mod[p] = set((x*x + y*y) % p for x in range(p) for y in range(p))

def is_sum_of_two_squares_fast(n):
    if n < 0: return False
    if n == 0 or n == 1: return True
    m8 = n % 8
    if m8 in {3, 6, 7}: return False
    for p, allowed in allowed_mod.items():
        if (n % p) not in allowed:
            return False
    factors = factorint(n)
    for p, exp in factors.items():
        if p % 4 == 3 and exp % 2 != 0:
            return False
    return True

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
# p=3 r=1
# p=7 r=15
# p=11 r=2
# p=19 r=41
# p=23 r=120
# p=31 r=225
moduli = [9, 121, 361, 529, 961]
residues = [1, 2, 41, 120, 225]

n_base, prod = crt(moduli, residues)
n_base = int(n_base)
prod = int(prod)

print(f"Base CRT solved: N0 = {n_base}, prod = {prod}")
sys.stdout.flush()

for k in range(1, 100000):
    N = n_base + k * prod
    if N % 2 == 0:
        continue
    N2 = N * N
    
    # We want N^2 < 1.62 * 10^48, so N < 1.27 * 10^24.
    # Since prod = 9.8 * 10^12, N will be well below the limit for k up to 10^10.
    if N >= 1.27 * 10**24:
        print("N exceeded the limit of 1.27 * 10^24!")
        break
        
    V_all = get_V_all(N2)
    any_sol = False
    for v in V_all:
        if is_sum_of_two_squares_fast(N2 - v):
            any_sol = True
            break
            
    if not any_sol:
        print(f"\nSUCCESS! FOUND TRUE COUNTEREXAMPLE N = {N}")
        print(f"N^2 = {N2}")
        print(f"k = {k}")
        print(f"V_all size = {len(V_all)}")
        sys.stdout.flush()
        
        # Now find a blocking prime for each v in V_all
        blocking_primes = {}
        all_primes_pool = [p for p in range(3, 50000) if isprime(p) and p % 4 == 3]
        all_covered = True
        for v in V_all:
            diff = N2 - v
            found_prime = -1
            # Check 3 and 7, then the other CRT primes, then the pool
            for p in [3, 7, 11, 19, 23, 31] + all_primes_pool:
                if diff % p == 0 and diff % (p**2) != 0:
                    found_prime = p
                    break
            if found_prime != -1:
                blocking_primes[v] = found_prime
            else:
                print(f"Failed to find blocking prime for v = {v}!")
                all_covered = False
                break
                
        if all_covered:
            print("SUCCESS! All elements blocked!")
            with open("/workspace/leanproject/Submission/success_counterexample.py", "w") as f:
                f.write(f"N = {N}\n")
                f.write(f"blocking_primes = {blocking_primes}\n")
            break
        else:
            print("Not all covered, continuing search...")
            sys.stdout.flush()
            
    if k % 100 == 0:
         print(f"Checked up to k = {k} (N has {len(str(N))} digits)...", flush=True)
