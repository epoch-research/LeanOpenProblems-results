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

primes_3mod4 = [p for p in range(11, 2000) if isprime(p) and p % 4 == 3]

# We want to find a set of primes such that the product of their squares is < 1.27 * 10**24
# Wait, product of squares of [11, 19, 23, 31, 43, 47, 59] is:
# (11*19*23*31*43*47*59)**2 = 1.05 * 10**20 < 10**24.
# So we can use up to 7 or 8 primes.

def search():
    moduli = [9, 49]
    residues = [1, 15]
    res_dict = {3: 1, 7: 15}
    used_primes = []
    prod = 441
    
    # We will do a greedy search but with a larger candidate pool of 50 primes
    step = 1
    while True:
        V_all = get_V_all(prod**2)
        unblocked = []
        for v in V_all:
            blocked_by_some = False
            for p, r in res_dict.items():
                n2_mod_p2 = (r*r) % (p**2)
                val_mod_p2 = (n2_mod_p2 - v) % (p**2)
                if val_mod_p2 % p == 0 and val_mod_p2 != 0:
                    blocked_by_some = True
                    break
            if not blocked_by_some:
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
            return True
            
        if prod >= 1.27 * 10**24:
            print("Prod exceeded 1.27 * 10**24! Failed.")
            return False
            
        best_p = None
        best_r = None
        best_blocked_count = -1
        
        available_primes = [p for p in primes_3mod4 if p not in res_dict]
        # To make it fast, we look at the first 50 available primes
        for p in available_primes[:50]:
            # If multiplying by p**2 exceeds the limit, skip
            if prod * (p**2) >= 1.27 * 10**24:
                continue
                
            roots_mod_p = set()
            for v in unblocked:
                v_mod_p = v % p
                if v_mod_p == 0:
                    roots_mod_p.add(0)
                elif pow(v_mod_p, (p-1)//2, p) == 1:
                    for x in range(1, p):
                        if (x*x) % p == v_mod_p:
                            roots_mod_p.add(x)
                            roots_mod_p.add(p - x)
                            break
                            
            candidate_rs = []
            for r0 in roots_mod_p:
                for k in range(p):
                    candidate_rs.append(r0 + k*p)
                    
            for r in candidate_rs:
                blocked_count = 0
                n2_mod_p2 = (r*r) % (p**2)
                for v in unblocked:
                    val_mod_p2 = (n2_mod_p2 - v) % (p**2)
                    if val_mod_p2 % p == 0 and val_mod_p2 != 0:
                        blocked_count += 1
                if blocked_count > best_blocked_count:
                    best_blocked_count = blocked_count
                    best_p = p
                    best_r = r
                    
        if best_p is None:
            print("Could not find any prime within limit!")
            return False
            
        print(f"Adding p={best_p}, r={best_r} (blocks {best_blocked_count} elements)")
        moduli.append(best_p**2)
        residues.append(best_r)
        res_dict[best_p] = best_r
        used_primes.append((best_p, best_r))
        prod *= best_p**2
        step += 1

search()
