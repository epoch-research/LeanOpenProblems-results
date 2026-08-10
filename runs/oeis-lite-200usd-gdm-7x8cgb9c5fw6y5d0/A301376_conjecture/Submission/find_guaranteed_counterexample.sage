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

# Primes pool
primes_pool = [p for p in prime_range(3, 1000) if p % 4 == 3]

# We want to find a counterexample N_0.
# Let's greedily choose residues for the first 15 primes to cover v up to N_max^2.
# Let's say N_max is 1.2 * 10^24 (the absolute maximum limit).
N_max = int(1.2 * 10**24)
limit = N_max * N_max
V_target = [v for v in all_V if v < limit]
print(f"V_target size for 1.2 * 10^24: {len(V_target)}")

selected_primes = []
selected_residues = {}
uncovered = list(V_target)

# We will select primes until the product exceeds 1.1 * 10^24 or we reach 16 primes
num_primes = 15
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

if N0 >= 1.27 * 10**24:
    print("Warning: N0 is larger than the limit!")
    # If N0 is larger, we can subtract base_prod or reduce the number of primes
    sys.exit(0)

# Check N0
print("Verifying N0...", flush=True)
N2 = N0 * N0
V_actual = [v for v in all_V if v < N2]
print(f"V_actual size for N0: {len(V_actual)}")

all_blocked = True
blocking_primes = {}
start_time = time.time()

for idx, v in enumerate(V_actual):
    diff = N2 - v
    found_p = None
    for p in selected_primes:
        if diff % p == 0 and diff % (p*p) != 0:
            found_p = p
            break
    if found_p is None:
        # factor
        factors = factor(diff)
        for p, exp in factors:
            if p % 4 == 3 and exp % 2 != 0:
                found_p = int(p)
                break
    if found_p is not None:
        blocking_primes[v] = found_p
    else:
        print(f"Element {v} (idx {idx}) is NOT BLOCKED!")
        all_blocked = False
        break

if all_blocked:
    print(f"\nSUCCESS! N0 = {N0} is a VALID COUNTEREXAMPLE!")
    print(f"Number of distinct blocking primes used: {len(set(blocking_primes.values()))}")
    with open("/workspace/leanproject/Submission/success_sage_found.py", "w") as f:
        f.write(f"N = {N0}\n")
        f.write(f"blocking_primes = {blocking_primes}\n")
else:
    print("N0 was not a counterexample.")
