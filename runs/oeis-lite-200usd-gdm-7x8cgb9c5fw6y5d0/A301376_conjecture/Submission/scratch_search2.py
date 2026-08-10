import sys
import math
from collections import defaultdict
from sympy import isprime

def get_V_all_correct(limit, S_max=100, I_max=400):
    V = {1}
    for s in range(S_max):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        if fs >= limit:
            break
        for i in range(I_max):
            val = fs * 4**i
            if val >= limit:
                break
            V.add(val)
    return sorted(list(V))

primes_pool = [p for p in range(3, 10000) if isprime(p) and p % 4 == 3]

primes = [3, 7]
res_dict = {3: 1, 7: 15}
prod = 441

for step in range(1, 100):
    # Since solving CRT at each step is slow, we just approximate limit with prod^2
    limit = prod**2
    V_all_N = get_V_all_correct(limit)
    
    unblocked = []
    for v in V_all_N:
        blocked = False
        for p, r in res_dict.items():
            n2_mod_p2 = (r*r) % (p**2)
            val_mod_p2 = (n2_mod_p2 - v) % (p**2)
            if val_mod_p2 % p == 0 and val_mod_p2 != 0:
                blocked = True
                break
        if not blocked:
            unblocked.append(v)
            
    print(f"Step {step}: Prod digits: {len(str(prod))}, V_all size: {len(V_all_N)}, Unblocked: {len(unblocked)}")
    sys.stdout.flush()
    
    if len(unblocked) == 0:
        print(f"\nSUCCESS!!! FOUND TRUE COVER AT STEP {step}")
        print(f"Base primes = {primes}")
        print(f"Prod = {prod}")
        break
        
    best_p = None
    best_r = None
    best_blocked_count = -1
    
    for p in primes_pool:
        if p in res_dict:
            continue
            
        by_mod_p = defaultdict(list)
        for v in unblocked:
            by_mod_p[v % p].append(v)
            
        allowed_r_mod_p = set()
        for vp in by_mod_p.keys():
            if vp == 0:
                allowed_r_mod_p.add(0)
            elif pow(vp, (p-1)//2, p) == 1:
                r0 = pow(vp, (p+1)//4, p)
                allowed_r_mod_p.add(r0)
                allowed_r_mod_p.add(p-r0)
                        
        if not allowed_r_mod_p:
            continue
            
        for r0 in allowed_r_mod_p:
            r2_mod_p = (r0 * r0) % p
            candidates_v = by_mod_p[r2_mod_p]
            if not candidates_v:
                continue
                
            if r0 == 0:
                covered_blocked = sum(1 for v in candidates_v if (v % (p**2)) != 0)
                if covered_blocked > best_blocked_count:
                    best_blocked_count = covered_blocked
                    best_p = p
                    best_r = 0
            else:
                diff = (r2_mod_p - r0*r0) // p
                inv_2r0 = pow(2*r0, p-2, p)
                k1 = (diff * inv_2r0) % p
                r1 = (r0 + k1*p) % (p**2)
                
                r0_neg = p - r0
                diff_neg = (r2_mod_p - r0_neg*r0_neg) // p
                inv_2r0_neg = pow(2*r0_neg, p-2, p)
                k_neg = (diff_neg * inv_2r0_neg) % p
                r2 = (r0_neg + k_neg*p) % (p**2)
                
                for r in [r1, r2]:
                    r2_mod_p2 = (r * r) % (p**2)
                    covered_blocked = sum(1 for v in candidates_v if (v % (p**2)) != r2_mod_p2)
                    if covered_blocked > best_blocked_count:
                        best_blocked_count = covered_blocked
                        best_p = p
                        best_r = r
                        
    if not best_p:
        print("Failed to find any prime to cover remaining elements.")
        break
        
    primes.append(best_p)
    res_dict[best_p] = best_r
    prod *= best_p**2
