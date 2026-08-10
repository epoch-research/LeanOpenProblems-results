import sys
import math
from collections import defaultdict
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

def find_best_r_for_prime(p, unblocked):
    by_mod_p = defaultdict(list)
    for v in unblocked:
        by_mod_p[v % p].append(v)
        
    best_blocked = -1
    best_r = None
    
    for r0 in range(p):
        r2_mod_p = (r0 * r0) % p
        candidates = by_mod_p[r2_mod_p]
        if not candidates:
            continue
            
        bad_count = defaultdict(int)
        for v in candidates:
            if r0 == 0:
                if (v % (p**2)) == 0:
                    bad_count[0] += 1
            else:
                diff = (v - r0*r0) % (p**2)
                c = diff // p
                inv_2r0 = pow(2*r0, p-2, p)
                k = (c * inv_2r0) % p
                bad_count[k] += 1
                
        for k in range(p):
            blocked = len(candidates) - bad_count[k]
            if blocked > best_blocked:
                best_blocked = blocked
                best_r = r0 + k * p
                
    return best_blocked, best_r

primes_3mod4 = [p for p in range(3, 1000) if isprime(p) and p % 4 == 3]

best_unblocked = 99999

def dfs(depth, moduli, residues, prod, res_dict):
    global best_unblocked
    
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
            
    unblocked_count = len(unblocked)
    print(f"Depth {depth}: prod={prod}, V_all={len(V_all)}, unblocked={unblocked_count}")
    sys.stdout.flush()
    if unblocked_count < best_unblocked:
        best_unblocked = unblocked_count
        print(f"New best: {unblocked_count} unblocked at depth {depth}, prod={prod} (digits: {len(str(prod))})")
        sys.stdout.flush()
        
    if unblocked_count == 0:
        print("\nSUCCESS! FOUND COMPLETE COVER!")
        n, _ = crt(moduli, residues)
        n = int(n)
        if n % 2 == 0:
            n += prod
        print(f"N = {n}")
        print(f"N_digits = {len(str(n))}")
        print(f"moduli = {moduli}")
        print(f"residues = {residues}")
        sys.exit(0)
        
    if prod >= 1.27 * 10**24:
        return
        
    available_primes = [p for p in primes_3mod4 if p not in res_dict]
    
    candidates = []
    for p in available_primes[:50]:
        if prod * (p**2) >= 1.27 * 10**24:
            continue
        blocked, r = find_best_r_for_prime(p, unblocked)
        if blocked > 0:
            candidates.append((blocked, p, r))
            
    # Sort by blocked count descending
    candidates.sort(key=lambda x: x[0], reverse=True)
    
    # Try the top candidates
    for blocked, p, r in candidates[:3]:
        new_moduli = moduli + [p**2]
        new_residues = residues + [r]
        new_res_dict = res_dict.copy()
        new_res_dict[p] = r
        dfs(depth + 1, new_moduli, new_residues, prod * (p**2), new_res_dict)

dfs(0, [9, 49], [1, 15], 441, {3: 1, 7: 15})
print("Search finished.")
