import sys
import math
from sympy import isprime, factorint
from sympy.ntheory.modular import crt

# Precompute allowed residues for sums of two squares modulo small primes
allowed_mod = {}
for p in [3, 7, 11, 19, 23, 31, 43, 47]:
    allowed_mod[p] = set((x*x + y*y) % p for x in range(p) for y in range(p))

def is_sum_of_two_squares_fast(n):
    if n < 0: return False
    if n == 0 or n == 1: return True
    # Pre-filters
    m8 = n % 8
    if m8 in {3, 6, 7}: return False
    for p, allowed in allowed_mod.items():
        if (n % p) not in allowed:
            return False
            
    # If it passes, factor it
    factors = factorint(n)
    for p, exp in factors.items():
        if p % 4 == 3 and exp % 2 != 0:
            return False
    return True

def has_solution_fast(N):
    max_v = int(math.log2(2*N)) + 2
    for v in range(max_v):
        for u in range(v + 1):
            if (2**v - 2**u) % 6 == 0:
                x = (2**v + 2**u) // 2
                y = (2**v - 2**u) // 6
                val = x*x + y*y
                if val <= N*N:
                    k = (u + v) // 2
                    if k <= N:
                        rem = N*N - val
                        if is_sum_of_two_squares_fast(rem):
                            return True
    return False

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

# Fixed residues from step 4 of greedy search
# p=3: r=1
# p=7: r=15
# p=11: r=2
# p=19: r=41 (or let's check greedy output of Step 2: p=11 r=2, Step 3: p=31 r=225)
# Let's use the actual successful residues from find_fixed_cover_fast.py:
# p=3 r=1
# p=11 r=2
# p=19 r=41
# p=23 r=120
# p=31 r=225
moduli = [9, 121, 361, 529, 961]
residues = [1, 2, 41, 120, 225]

n_base, prod = crt(moduli, residues)
n_base = int(n_base)
prod = int(prod)

print(f"Base CRT solved: N0 = {n_base}, prod = {prod} (digits: {len(str(prod))})")
sys.stdout.flush()

# We start searching for N = n_base + k * prod
# We want N to be odd, so we can adjust step if prod is even or odd (prod is odd because all moduli are odd)
# So N can be even or odd. If we want N to be odd, we check and skip even ones.
for k in range(1, 100000):
    if k % 10 == 0:
        print(f"Checking k = {k}...", flush=True)
    N = n_base + k * prod
    if N % 2 == 0:
        continue
        
    # Check if N has any solution
    if not has_solution_fast(N):
        print(f"\nFOUND TRUE COUNTEREXAMPLE N = {N}")
        print(f"N^2 = {N*N}")
        sys.stdout.flush()
        
        # Verify and find blocking primes
        N2 = N * N
        V_all = get_V_all(N2)
        print(f"V_all size: {len(V_all)}")
        
        blocking_primes = {}
        all_primes_pool = [p for p in range(3, 10000) if isprime(p) and p % 4 == 3]
        
        all_covered = True
        for v in V_all:
            diff = N2 - v
            found_prime = -1
            for p in all_primes_pool:
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
            print(f"Primes count: {len(set(blocking_primes.values()))}")
            # Save the result to a python file
            with open("/workspace/leanproject/Submission/success_counterexample.py", "w") as f:
                f.write(f"N = {N}\n")
                f.write(f"blocking_primes = {blocking_primes}\n")
            break
        else:
            print("Not all covered, continuing search...")
            sys.stdout.flush()
