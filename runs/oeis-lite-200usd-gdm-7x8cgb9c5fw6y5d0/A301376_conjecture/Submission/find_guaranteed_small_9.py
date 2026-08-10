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

# Primes pool
primes_pool = [p for p in range(3, 150) if isprime(p) and p % 4 == 3]

# We will search for a subset of primes_pool
# To make it fast, we can use a recursive backtracking search
best_unblocked_count = 999999

def search(primes, res_dict, prod):
    global best_unblocked_count
    limit = prod**2
    V_all = get_V_all(limit)
    
    # Calculate unblocked
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
    if unblocked_count == 0:
        print("\nFOUND COMPLETE COVER!")
        print("Primes:", primes)
        print("Res dict:", res_dict)
        print("Prod:", prod)
        n, _ = crt([p**2 for p in primes], [res_dict[p] for p in primes])
        n = int(n)
        if n % 2 == 0:
            n += prod
        print("n0 =", n)
        print("n0^2 =", n*n)
        sys.exit(0)
        
    if prod**2 >= 1.6 * 10**48: # we must keep N^2 < 1.6 * 10^48, so prod < 1.26 * 10^24
        return
        
    if len(primes) >= 12: # limit depth to 12 primes
        return
        
    # Choose next prime
    # Sort remaining primes by how many they can cover
    candidates = []
    for p in primes_pool:
        if p in res_dict:
            continue
        if prod * (p**2) >= 1.26 * 10**24:
            continue
            
        # Find best residue for p
        roots = set()
        for v in unblocked:
            v_mod_p = v % p
            if v_mod_p == 0:
                roots.add(0)
            elif pow(v_mod_p, (p-1)//2, p) == 1:
                for x in range(1, p):
                    if (x*x) % p == v_mod_p:
                        roots.add(x)
                        roots.add(p-x)
                        break
        best_r = None
        best_cov = 0
        for r0 in roots:
            for k in range(p):
                r = r0 + k*p
                cov = sum(1 for v in unblocked if (r*r - v) % p == 0 and (r*r - v) % (p**2) != 0)
                if cov > best_cov:
                    best_cov = cov
                    best_r = r
                    
        if best_cov > 0:
            candidates.append((best_cov, p, best_r))
            
    # Sort candidates by count descending
    candidates.sort(key=lambda x: x[0], reverse=True)
    
    # Recurse on top candidates
    for cov, p, r in candidates[:4]:
        new_primes = primes + [p]
        new_res_dict = res_dict.copy()
        new_res_dict[p] = r
        search(new_primes, new_res_dict, prod * (p**2))

# Start search with {3: 1, 7: 15}
search([3, 7], {3: 1, 7: 15}, 441)
print("Search finished.")
