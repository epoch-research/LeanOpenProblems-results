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

limit = 10**44
V_all = get_V_all(limit)
print(f"Fixed limit: {limit}")
print(f"V_all size: {len(V_all)}")

# Primes pool in a fixed order to process one-by-one
primes_pool = [7, 11, 19, 23, 31, 43, 47, 59, 67, 71, 79, 83, 103, 107, 127, 131, 139, 151, 163, 167, 179, 191, 199, 211, 223, 227, 239, 251, 263, 271, 283, 307, 311, 331, 347, 359, 367, 379, 383]

uncovered = set(V_all)
res_dict = {3: 1} # p=3, r=1 covers powers of 4
uncovered -= set(v for v in uncovered if v % 3 == 1)
print(f"After p=3, r=1: {len(uncovered)} uncovered.")

prod = 9
used_primes = [3]

for p in primes_pool:
    if not uncovered:
        break
        
    # Find square roots mod p of currently uncovered elements
    roots = set()
    for v in uncovered:
        v_mod_p = v % p
        if v_mod_p == 0:
            roots.add(0)
        elif pow(v_mod_p, (p-1)//2, p) == 1:
            # Find square root
            for x in range(1, p):
                if (x*x) % p == v_mod_p:
                    roots.add(x)
                    roots.add(p-x)
                    break
                    
    if not roots:
        continue
        
    # For each root, try its p lifts
    best_p_r = None
    best_p_covered = set()
    for r0 in roots:
        for k in range(p):
            r = r0 + k*p
            # Count how many uncovered are blocked
            covered_blocked = set()
            n2_mod_p2 = r*r
            for v in uncovered:
                val_mod_p2 = (n2_mod_p2 - v) % (p**2)
                if val_mod_p2 % p == 0 and val_mod_p2 != 0:
                    covered_blocked.add(v)
            if len(covered_blocked) > len(best_p_covered):
                best_p_covered = covered_blocked
                best_p_r = r
                
    if len(best_p_covered) > 0:
        res_dict[p] = best_p_r
        uncovered -= best_p_covered
        prod *= p**2
        used_primes.append(p)
        print(f"Added p={p}, r={best_p_r} (covers {len(best_p_covered)}). Uncovered remaining: {len(uncovered)}. Current prod digits: {len(str(prod))}")
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
    print(f"N < 1.26 * 10**24? {n < 1.26 * 10**24}")
