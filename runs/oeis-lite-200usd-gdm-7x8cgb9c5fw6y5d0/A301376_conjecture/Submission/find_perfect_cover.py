import sys
import math
import itertools
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

# Candidate primes congruent to 3 mod 4
primes_pool = [11, 19, 23, 31, 43, 47, 59, 67, 71, 79]
print("Primes pool:", primes_pool)

# Base primes
base_res = {3: 1, 7: 15}

# Find covers of sizes 4, 5, 6
for k in range(4, 9):
    print(f"\n--- Searching for subsets of size {k} ---")
    sys.stdout.flush()
    
    # Generate combinations and sort by product
    combos = []
    for combo in itertools.combinations(primes_pool, k):
        prod = 21
        for p in combo:
            prod *= p
        combos.append((prod, combo))
    combos.sort(key=lambda x: x[0])
    
    for prod, combo in combos:
        if prod >= 1.26e24:
            # Too large to guarantee s < 40, i < 160
            continue
            
        limit = prod**2
        V_all = get_V_all(limit)
        
        # Filter out elements blocked by 3 and 7
        uncovered = set()
        for v in V_all:
            blocked = False
            for p, r in base_res.items():
                if (r*r - v) % p == 0 and (r*r - v) % (p**2) != 0:
                    blocked = True
                    break
            if not blocked:
                uncovered.add(v)
                
        # If no uncovered elements, then 3 and 7 are enough (unlikely)
        if len(uncovered) == 0:
            print(f"SUCCESS with 3 and 7 alone! Prod = {prod}")
            # Solve CRT and exit...
            
        # Backtracking search to cover 'uncovered' using 'combo'
        primes = list(combo)
        
        def dfs(idx, current_res_dict, current_uncovered):
            if len(current_uncovered) == 0:
                return current_res_dict
            if idx >= len(primes):
                return None
                
            p = primes[idx]
            # Find candidate roots mod p
            roots_mod_p = set()
            for v in current_uncovered:
                v_mod_p = v % p
                if v_mod_p == 0:
                    roots_mod_p.add(0)
                elif pow(v_mod_p, (p-1)//2, p) == 1:
                    # Find square roots
                    for x in range(1, p):
                        if (x*x) % p == v_mod_p:
                            roots_mod_p.add(x)
                            roots_mod_p.add(p - x)
                            break
                            
            # Check candidate residues r = r0 + m*p
            for r0 in roots_mod_p:
                for m in range(p):
                    r = r0 + m*p
                    # Check which elements of current_uncovered are blocked by this (p, r)
                    blocked_by_pr = set()
                    for v in current_uncovered:
                        if (r*r - v) % p == 0 and (r*r - v) % (p**2) != 0:
                            blocked_by_pr.add(v)
                            
                    if len(blocked_by_pr) > 0:
                        new_res_dict = current_res_dict.copy()
                        new_res_dict[p] = r
                        res = dfs(idx + 1, new_res_dict, current_uncovered - blocked_by_pr)
                        if res is not None:
                            return res
            return None
            
        res = dfs(0, base_res.copy(), uncovered)
        if res is not None:
            print(f"SUCCESS! Found guaranteed cover!")
            print(f"Primes: {res.keys()}")
            print(f"Residues: {res}")
            print(f"Product of primes: {prod}")
            print(f"Product of squares: {prod**2}")
            
            # Solve CRT to find N
            moduli = [p**2 for p in res]
            residues = [res[p] for p in res]
            n, pr_sq = crt(moduli, residues)
            n = int(n)
            if n % 2 == 0:
                n += pr_sq
            print(f"n0 = {n}")
            print(f"n0^2 = {n**2}")
            sys.exit(0)
            
