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

# Run greedy search for a few steps to get a base N
primes_pool = [p for p in range(3, 300) if isprime(p) and p % 4 == 3]

primes = [3, 7]
res_dict = {3: 1, 7: 15}
prod = 441

for step in range(1, 9):
    limit = prod**2
    V_all = get_V_all(limit)
    
    unblocked = []
    for v in V_all:
        blocked = False
        for p, r in res_dict.items():
            n2_mod_p2 = (r*r) % (p**2)
            val_mod_p2 = (n2_mod_p2 - v) % (p**2)
            if val_mod_p2 % p == 0 and val_mod_p2 != 0:
                blocked = True
                break
        if not blocked:
            unblocked.append(v)
            
    # Solve CRT to find N for this step
    moduli = [p**2 for p in primes]
    residues = [res_dict[p] for p in primes]
    n0, pr_sq = crt(moduli, residues)
    n0 = int(n0)
    if n0 % 2 == 0:
        n0 += pr_sq
        
    print(f"Step {step}: Base primes = {primes}, N = {n0} (digits: {len(str(n0))})")
    
    # Check if this N can be completely blocked by primes up to 2000
    N2 = n0**2
    V_all_N = get_V_all(N2)
    
    unblocked_N = []
    blocking_primes_found = {}
    
    all_primes_pool = [p for p in range(3, 2000) if isprime(p) and p % 4 == 3]
    
    all_covered = True
    for v in V_all_N:
        # Check if v is blocked by some prime in all_primes_pool
        blocked_by = -1
        for p in all_primes_pool:
            diff = N2 - v
            if diff % p == 0 and diff % (p**2) != 0:
                blocked_by = p
                break
        if blocked_by != -1:
            blocking_primes_found[v] = blocked_by
        else:
            unblocked_N.append(v)
            all_covered = False
            
    print(f"  V_all(N^2) size: {len(V_all_N)}, Unblocked: {len(unblocked_N)}")
    if all_covered:
        print(f"  SUCCESS! N = {n0} is a complete counterexample!")
        print(f"  Primes used for blocking: {sorted(list(set(blocking_primes_found.values())))}")
        # print the mapping from v to prime
        sys.exit(0)
        
    # Choose next best prime for greedy search
    best_p = None
    best_r = None
    best_cov = -1
    for p in primes_pool:
        if p in res_dict:
            continue
        block_count = [0] * (p**2)
        for v in unblocked:
            v_mod_p = v % p
            if v_mod_p == 0:
                if (v % (p**2)) != 0:
                    for k in range(p):
                        block_count[k * p] += 1
            else:
                if pow(v_mod_p, (p-1)//2, p) == 1:
                    r0 = -1
                    for x in range(1, p):
                        if (x*x) % p == v_mod_p:
                            r0 = x
                            break
                    if r0 != -1:
                        roots = [r0, p - r0]
                        for rt in roots:
                            d = (v - rt**2) // p
                            inv_2rt = pow(2 * rt, p - 2, p)
                            k_bad = (d * inv_2rt) % p
                            for k in range(p):
                                if k != k_bad:
                                    block_count[rt + k * p] += 1
        max_cov = max(block_count)
        best_r_for_p = block_count.index(max_cov)
        if max_cov > best_cov:
            best_cov = max_cov
            best_p = p
            best_r = best_r_for_p
            
    primes.append(best_p)
    res_dict[best_p] = best_r
    print(f"  Current res_dict: {res_dict}")
    prod *= best_p**2
