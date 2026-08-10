import math
import sys
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

limit = 10**24
V_all = get_V_all(limit)
print(f"V_all size for limit {limit}: {len(V_all)}")

primes_pool = [p for p in range(11, 1000) if isprime(p) and p % 4 == 3]

res_dict = {3: 1, 7: 15}
prod = 441
used_primes = [3, 7]

uncovered = set(V_all)
blocked_3_7 = set()
for v in uncovered:
    blocked = False
    for p, r in res_dict.items():
        n2_mod_p2 = (r*r) % (p**2)
        val_mod_p2 = (n2_mod_p2 - v) % (p**2)
        if val_mod_p2 % p == 0 and val_mod_p2 != 0:
            blocked = True
            break
    if blocked:
        blocked_3_7.add(v)
uncovered -= blocked_3_7
print(f"After [3, 7], uncovered: {len(uncovered)}")

while uncovered:
    best_p = None
    best_r = None
    best_covered = set()
    best_score = -1
    
    # We search ALL available primes in the pool
    for p in primes_pool:
        if p in res_dict:
            continue
        if prod * (p**2) >= 1.26 * 10**24:
            continue
            
        roots = set()
        for v in uncovered:
            v_mod_p = v % p
            if v_mod_p == 0:
                roots.add(0)
            elif pow(v_mod_p, (p-1)//2, p) == 1:
                for x in range(1, p):
                    if (x*x) % p == v_mod_p:
                        roots.add(x)
                        roots.add(p-x)
                        break
                        
        if not roots:
            continue
            
        best_p_r = None
        best_p_covered = set()
        for r0 in roots:
            for k in range(p):
                r = r0 + k*p
                covered_blocked = set(v for v in uncovered if (r*r - v) % p == 0 and (r*r - v) % (p**2) != 0)
                if len(covered_blocked) > len(best_p_covered):
                    best_p_covered = covered_blocked
                    best_p_r = r
                    
        if len(best_p_covered) > 0:
            # Score: we want to maximize elements covered per log(p^2) unit of product increase
            score = len(best_p_covered) / math.log(p**2)
            if score > best_score:
                best_score = score
                best_p = p
                best_r = best_p_r
                best_covered = best_p_covered
                
    if not best_p:
        print("Failed to find any prime to cover remaining elements within limit.")
        break
        
    res_dict[best_p] = best_r
    uncovered -= best_covered
    prod *= best_p**2
    used_primes.append(best_p)
    print(f"Added p={best_p}, r={best_r} (covers {len(best_covered)}). Uncovered remaining: {len(uncovered)}. Current prod digits: {len(str(prod))}")
    sys.stdout.flush()

if not uncovered:
    print("\nSUCCESS!")
    moduli = [p**2 for p in used_primes]
    residues = [res_dict[p] for p in used_primes]
    n, prod = crt(moduli, residues)
    n = int(n)
    if n % 2 == 0:
        n += prod
    print(f"n0 = {n}")
    print(f"n0^2 = {n*n}")
    print(f"used_primes = {used_primes}")
    print(f"res_dict = {res_dict}")
