import sys
import math
from collections import defaultdict
from sympy import isprime
from sympy.ntheory.modular import crt

def get_V_all(limit, S_bound, I_bound):
    V = {1}
    for s in range(S_bound):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        if fs >= limit:
            break
        for i in range(I_bound):
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

primes_3mod4 = [p for p in range(3, 10000) if isprime(p) and p % 4 == 3]

# Start with [3, 7]
moduli = [9, 49]
residues = [1, 15]
res_dict = {3: 1, 7: 15}
used_primes = []
prod = 441
step = 1

while True:
    limit = prod**2
    # S_bound is smallest s such that 16^s >= limit
    # 16^s >= limit => s * log(16) >= log(limit) => s >= log(limit)/log(16)
    S_bound = int(math.ceil(math.log(limit) / math.log(16)))
    I_bound = int(math.ceil(math.log(limit) / math.log(4)))
    
    V_all = get_V_all(limit, S_bound, I_bound)
    
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
            
    print(f"Step {step}: Prod={prod} (digits: {len(str(prod))}), S_bound={S_bound}, I_bound={I_bound}, V_all={len(V_all)}, Unblocked={len(unblocked)}")
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
        sys.exit(0)
        
    best_p = None
    best_r = None
    best_blocked_count = -1
    
    available_primes = [p for p in primes_3mod4 if p not in res_dict]
    
    # We look at available primes and select the best one
    for p in available_primes[:200]:
        blocked, r = find_best_r_for_prime(p, unblocked)
        if blocked > best_blocked_count:
            best_blocked_count = blocked
            best_p = p
            best_r = r
            
    if best_p is None:
        print("Could not find any prime!")
        break
        
    print(f"Adding p={best_p}, r={best_r} (blocks {best_blocked_count} elements)")
    moduli.append(best_p**2)
    residues.append(best_r)
    res_dict[best_p] = best_r
    used_primes.append((best_p, best_r))
    prod *= best_p**2
    step += 1
