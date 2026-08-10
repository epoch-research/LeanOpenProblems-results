import sys
import math
from collections import defaultdict
from sympy import isprime
from sympy.ntheory.modular import crt

# N <= 10^22 (prod <= 10^22)
# S_max = 40, I_max = 80 => total cases = 3200
PROD_LIMIT = 10**22

def get_V_all(limit):
    V = {1}
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        if fs >= limit:
            break
        for i in range(80):
            val = fs * 4**i
            if val >= limit:
                break
            V.add(val)
    return sorted(list(V))

primes_3mod4 = [p for p in range(3, 100000) if isprime(p) and p % 4 == 3]

moduli = [9, 49]
residues = [1, 15]
res_dict = {3: 1, 7: 15}
used_primes = []
prod = 441
step = 1

while True:
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
            
    print(f"Step {step}: Prod={prod} (digits: {len(str(prod))}), V_all={len(V_all)}, Unblocked={len(unblocked)}")
    sys.stdout.flush()
    
    if len(unblocked) == 0:
        print("\nSUCCESS! ALL ELEMENTS BLOCKED!")
        n, _ = crt(moduli, residues)
        n = int(n)
        if n % 2 == 0:
            n += prod
        print(f"n0 = {n}")
        print(f"n0_digits = {len(str(n))}")
        print(f"used_primes = {used_primes}")
        print(f"res_dict = {res_dict}")
        sys.exit(0)
        
    if prod >= PROD_LIMIT:
        print("Prod exceeded limit! Failed.")
        break
        
    best_p = None
    best_r = None
    best_blocked_count = -1
    
    available_primes = [p for p in primes_3mod4 if p not in res_dict]
    # Check first 2000 available primes
    for p in available_primes[:2000]:
        if prod * (p**2) >= PROD_LIMIT:
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
                allowed_r_mod_p.add(p - r0)
                
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
                        
    if best_p is None:
        print("Could not find any prime within limit!")
        break
        
    print(f"Adding p={best_p}, r={best_r} (blocks {best_blocked_count} elements)")
    moduli.append(best_p**2)
    residues.append(best_r)
    res_dict[best_p] = best_r
    used_primes.append((best_p, best_r))
    prod *= best_p**2
    step += 1
