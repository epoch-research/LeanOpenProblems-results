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

# Pool of very small primes = 3 mod 4
primes_pool = [3, 7, 11, 19, 23, 31, 43, 47, 59, 67, 71, 79, 83]

# We want N_max to be around 10^13
N_max = 5 * 10**12
limit = N_max * N_max
V_target = [v for v in all_V if v < limit]
print(f"V_target size for 5 * 10^12: {len(V_target)}")

selected_primes = []
selected_residues = {}
uncovered = list(V_target)

# Greedily pick 9 primes
num_primes = 9
for step in range(num_primes):
    best_p = None
    best_r = None
    best_cov = -1
    
    for p in primes_pool:
        if p in selected_primes:
            continue
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
        best_r_for_p = cov_for_r.index(max_cov)
        if max_cov > best_cov:
            best_cov = max_cov
            best_p = p
            best_r = best_r_for_p
            
    if best_cov <= 0:
        break
        
    selected_primes.append(best_p)
    selected_residues[best_p] = best_r
    new_uncovered = []
    r2 = (best_r * best_r) % best_p
    for v in uncovered:
        if v % best_p != r2:
            new_uncovered.append(v)
    uncovered = new_uncovered
    print(f"Selected Prime {best_p}, Residue {best_r} (covers {best_cov} elements). Uncovered remaining: {len(uncovered)}")

moduli = [2] + selected_primes
residues = [1] + [selected_residues[p] for p in selected_primes]
from math import prod as math_prod
base_prod = math_prod(moduli)
N0 = int(crt(residues, moduli))

print(f"CRT base: N0 = {N0}")
print(f"prod = {base_prod} (digits: {len(str(base_prod))})")

# Now check candidates N = N0 + k * base_prod
print("Searching for counterexample...", flush=True)
start_time = time.time()
found = False
for k in range(1000):
    N = N0 + k * base_prod
    if N <= 1:
        continue
    if N >= 1.27 * 10**24:
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
            # check small primes up to 1000
            for p in prime_range(3, 1000):
                if p % 4 == 3:
                    if diff % p == 0 and diff % (p*p) != 0:
                        found_p = int(p)
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
        print(f"\nSUCCESS! Found counterexample N = {N} (k = {k}) in {time.time() - start_time:.2f}s")
        print(f"N^2 = {N2}")
        print(f"V_all size = {len(V_actual)}")
        print(f"blocking_primes = {blocking_primes}")
        found = True
        
        with open("/workspace/leanproject/Submission/success_sage_found.py", "w") as f:
            f.write(f"N = {N}\n")
            f.write(f"blocking_primes = {blocking_primes}\n")
        break

if not found:
    print("No counterexample found.")
