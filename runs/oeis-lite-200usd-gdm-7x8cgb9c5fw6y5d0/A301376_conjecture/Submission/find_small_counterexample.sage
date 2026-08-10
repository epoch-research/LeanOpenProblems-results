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

N_max = 2 * 10**8
limit = N_max * N_max
V_target = [v for v in all_V if v < limit]

# We will use exactly 5 base primes
selected_primes = [3, 11, 31, 19, 23]
# Let's find the best residues for these 5 primes on V_target
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
    print(f"Prime {p}, residue {best_r} (uncovered remaining: {len(uncovered)})")

moduli = [2] + selected_primes
residues = [1] + [selected_residues[p] for p in selected_primes]
from math import prod as math_prod
base_prod = math_prod(moduli)
N0 = int(crt(residues, moduli))

print(f"CRT base: N0 = {N0}, prod = {base_prod}")

start_time = time.time()
found = False
for k in range(10000):
    N = N0 + k * base_prod
    if N <= 1:
        continue
    if N >= N_max:
        break
        
    N2 = N * N
    V_actual = [v for v in all_V if v < N2]
    
    all_blocked = True
    blocking_primes = {}
    for v in V_actual:
        diff = N2 - v
        found_p = None
        for p in selected_primes:
            if diff % p == 0 and diff % (p*p) != 0:
                found_p = p
                break
        if found_p is None:
            factors = factor(diff)
            for p, exp in factors:
                if p % 4 == 3 and exp % 2 != 0:
                    found_p = int(p)
                    break
        if found_p is not None:
            blocking_primes[v] = found_p
        else:
            all_blocked = False
            break
            
    if all_blocked:
        print(f"\nSUCCESS! Found N = {N} (k = {k}) in {time.time() - start_time:.2f}s")
        print(f"N^2 = {N2}")
        print(f"V_all size = {len(V_actual)}")
        print(f"blocking_primes = {blocking_primes}")
        found = True
        
        with open("/workspace/leanproject/Submission/success_sage_found.py", "w") as f:
            f.write(f"N = {N}\n")
            f.write(f"blocking_primes = {blocking_primes}\n")
        break

if not found:
    print(f"No counterexample found up to {N_max}")
