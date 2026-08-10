import sys
import math
from sympy import isprime, factorint

# Precompute allowed residues for sums of two squares modulo small primes
allowed_mod = {}
for p in [3, 7, 11, 19, 23, 31]:
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

# Search for N which is odd and multiple of 3
# to avoid v = N^2 solutions and simplify
print("Searching for tiny counterexample N...", flush=True)
for N in range(100005, 3140000, 6):
    if N % 10000 == 3:
        print(f"Checking N up to {N}...", flush=True)
        
    if not has_solution_fast(N):
        print(f"\nFOUND TINY COUNTEREXAMPLE N = {N}")
        print(f"N^2 = {N*N}")
        sys.stdout.flush()
        
        # Verify and find blocking primes
        N2 = N * N
        V_all = get_V_all(N2)
        print(f"V_all size: {len(V_all)}")
        
        blocking_primes = {}
        all_primes_pool = [3, 7, 11, 19, 23, 31, 43, 47, 59, 67, 71, 79, 83]
        
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
            print(f"Blocking primes mapping: {blocking_primes}")
            # Save the result to a python file
            with open("/workspace/leanproject/Submission/success_tiny.py", "w") as f:
                f.write(f"N = {N}\n")
                f.write(f"blocking_primes = {blocking_primes}\n")
            break
        else:
            print("Not all covered by small primes, continuing...")
            sys.stdout.flush()
            
print("Search finished.")
