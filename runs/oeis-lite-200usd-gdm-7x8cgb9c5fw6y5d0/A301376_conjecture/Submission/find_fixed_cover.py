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

# Fix limit to 10**44 (which ensures s < 37 and i < 73)
limit = 10**44
V_all = get_V_all(limit)
print(f"Fixed limit: {limit}")
print(f"V_all size: {len(V_all)}")

# We want to cover all of them using primes p = 3 mod 4
primes_pool = [p for p in range(3, 150) if isprime(p) and p % 4 == 3]

uncovered = set(V_all)
res_dict = {3: 1} # p=3, r=1 covers powers of 4
uncovered -= set(v for v in uncovered if v % 3 == 1)
print(f"After p=3, r=1: {len(uncovered)} uncovered.")

prod = 9
used_primes = [3]

while uncovered:
    best_p = None
    best_r = None
    best_covered = set()
    
    # We want to find a prime in the pool that covers the most elements relative to its size p**2
    # But since we want to minimize the product of p**2, we can just use a greedy score: len(covered) / log(p) or similar
    # Let's try to search among available primes
    for p in primes_pool:
        if p in res_dict:
            continue
            
        # Find best residue for p
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
                        
        best_p_r = None
        best_p_covered = set()
        for r0 in roots:
            for k in range(p):
                r = r0 + k*p
                covered = set(v for v in uncovered if ((r*r - v) % (p**2) == 0 and (r*r - v) % p == 0 and (r*r - v) != 0))
                # Wait, blocking condition: (N^2 - v) % p == 0 and (N^2 - v) % p^2 != 0
                # So (r^2 - v) % p == 0 but (r^2 - v) % p^2 != 0!
                covered_blocked = set(v for v in uncovered if (r*r - v) % p == 0 and (r*r - v) % (p**2) != 0)
                if len(covered_blocked) > len(best_p_covered):
                    best_p_covered = covered_blocked
                    best_p_r = r
                    
        if len(best_p_covered) > 0:
            # Score: we want to maximize len(best_p_covered) / log(p**2)
            score = len(best_p_covered) / math.log(p**2)
            if best_p is None or score > best_score:
                best_score = score
                best_p = p
                best_r = best_p_r
                best_covered = best_p_covered
                
    if not best_p:
        print("Failed to find any prime to cover remaining elements.")
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
    print(f"N < 1.26 * 10**24? {n < 1.26 * 10**24}")
