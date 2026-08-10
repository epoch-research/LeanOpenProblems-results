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
primes_pool = [p for p in range(3, 1000) if isprime(p) and p % 4 == 3]

primes = [3, 7]
res_dict = {3: 1, 7: 15}
prod = 441 # product of squares of primes

step = 1
while True:
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
            
    print(f"Step {step}: prod = {prod} (digits of prod: {len(str(prod))}), V_all size: {len(V_all)}, unblocked size: {len(unblocked)}")
    sys.stdout.flush()
    
    if len(unblocked) == 0:
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
        break
        
    if prod**2 >= 1.6 * 10**48:
        print("Exceeded limit!")
        break
        
    # Choose next best prime and residue
    best_p = None
    best_r = None
    best_cov = -1
    
    for p in primes_pool:
        if p in res_dict:
            continue
        if prod * (p**2) >= 1.26 * 10**24:
            continue
            
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
        for r0 in roots:
            for k in range(p):
                r = r0 + k*p
                cov = sum(1 for v in unblocked if (r*r - v) % p == 0 and (r*r - v) % (p**2) != 0)
                if cov > best_cov:
                    best_cov = cov
                    best_p = p
                    best_r = r
                    
    if best_p is None or best_cov <= 0:
        print("No progress possible!")
        break
        
    primes.append(best_p)
    res_dict[best_p] = best_r
    prod *= best_p**2
    step += 1
