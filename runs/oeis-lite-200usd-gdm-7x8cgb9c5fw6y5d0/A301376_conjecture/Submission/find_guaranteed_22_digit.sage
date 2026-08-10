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
small_primes = [p for p in prime_range(3, 2000) if p % 4 == 3]

# 12 base primes
selected_primes = [3, 11, 31, 43, 127, 23, 19, 59, 71, 83, 47, 67]

# We optimize residues for N up to 10^22 (which is under 1.2 * 10^24)
N_max = 10**22
limit = N_max * N_max
V_target = [v for v in all_V if v < limit]
print(f"V_target size for 10^22: {len(V_target)}")

selected_residues = {}
uncovered = list(V_target)

for p in selected_primes:
    cov_for_r = [0] * p
    for v in uncovered:
        v_mod = v % p
        if v_mod == 0:
            cov_for_r[0] += 1
        elif pow(v_mod, (p-1)//2, p) == 1:
            for r in range(1, p):
                if (r*r) % p == v_mod:
                    cov_for_r[r] += 1
                    cov_for_r[p-r] += 1
                    break
    max_cov = max(cov_for_r)
    best_r = cov_for_r.index(max_cov)
    selected_residues[p] = best_r
    
    # Remove covered
    new_uncovered = []
    r2 = (best_r * best_r) % p
    for v in uncovered:
        if v % p != r2:
            new_uncovered.append(v)
    uncovered = new_uncovered
    print(f"Selected Prime {p}, Residue {best_r} (uncovered remaining: {len(uncovered)})")

moduli = [2] + selected_primes
residues = [1] + [selected_residues[p] for p in selected_primes]
from math import prod as math_prod
base_prod = math_prod(moduli)
N0 = int(crt(residues, moduli))

print(f"CRT base: N0 = {N0}")
print(f"prod = {base_prod} (digits: {len(str(base_prod))})")

if N0 >= 1.27 * 10**24:
    print("Exceeded limit!")
    sys.exit(0)

def is_blocked_fast(diff):
    for p in selected_primes:
        if diff % p == 0:
            if diff % (p*p) != 0:
                return p
    for p in small_primes:
        if diff % p == 0:
            if diff % (p*p) != 0:
                return p
    # Fallback to Sage factor
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
            return None
        blocking_primes[v] = p
    return blocking_primes

print("Searching for counterexample...", flush=True)
start_time = time.time()
found = False

for k in range(5000):
    N = N0 + k * base_prod
    if N <= 1:
        continue
    if N >= 1.27 * 10**24:
        break
        
    bp = check_candidate(N)
    if bp is not None:
        print(f"\nSUCCESS! Found counterexample N = {N} (k = {k}) in {time.time() - start_time:.2f}s")
        print(f"N^2 = {N2}")
        print(f"V_all size = {len([v for v in all_V if v < N*N])}")
        print(f"blocking_primes = {bp}")
        found = True
        
        with open("/workspace/leanproject/Submission/success_sage_found.py", "w") as f:
            f.write(f"N = {N}\n")
            f.write(f"blocking_primes = {bp}\n")
        break

if not found:
    print("No counterexample found.")
