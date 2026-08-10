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

# We want a perfect cover for limit = 10**48 (or slightly less, say 1.25 * 10**48)
# Let's set limit to 1.62 * 10**48
limit = 162 * 10**46
V_all = get_V_all(limit)
print(f"V_all size for limit {limit}: {len(V_all)}")
sys.stdout.flush()

# Candidate primes: we can use primes congruent to 3 mod 4
primes_pool = [3, 7, 11, 19, 23, 31, 43, 47, 59, 67, 71, 79, 83]

# We will run a greedy search, but we can also backtrack or try multiple random choices
# Let's do a randomized/greedy search to find if ANY combination of 9 primes can cover V_all
import random
random.seed(42)

for trial in range(10000):
    # Try a greedy search with some randomness
    res_dict = {}
    used_primes = []
    prod = 1
    uncovered = set(V_all)
    
    # We always start with 3 and 7 because they are very small and cover a lot
    res_dict[3] = 1
    res_dict[7] = 15
    used_primes = [3, 7]
    prod = 441
    
    # Remove elements covered by 3 and 7
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
    
    # Now choose the remaining primes
    success = True
    while uncovered:
        if len(used_primes) >= 9:
            success = False
            break
            
        # Find all available primes
        available = [p for p in primes_pool if p not in res_dict]
        if not available:
            success = False
            break
            
        # For each available prime, find the best residue
        best_p = None
        best_r = None
        best_covered = set()
        
        # To add some randomness, we can shuffle available or pick from the top 3
        # Let's evaluate all of them
        candidates = []
        for p in available:
            # Group uncovered by v % p
            by_mod = {}
            for v in uncovered:
                by_mod[v % p] = by_mod.get(v % p, []) + [v]
            
            # Find QR roots mod p
            roots = set()
            for vp in by_mod.keys():
                if vp == 0:
                    roots.add(0)
                elif pow(vp, (p-1)//2, p) == 1:
                    for x in range(1, p):
                        if (x*x) % p == vp:
                            roots.add(x)
                            roots.add(p-x)
                            break
            if not roots:
                continue
                
            for r0 in roots:
                for k in range(p):
                    r = r0 + k*p
                    r2 = (r*r) % (p**2)
                    covered = set(v for v in by_mod.get((r*r)%p, []) if (v % (p**2)) != r2)
                    if covered:
                        candidates.append((len(covered), p, r, covered))
                        
        if not candidates:
            success = False
            break
            
        # Sort candidates by number of covered elements
        candidates.sort(key=lambda x: x[0], reverse=True)
        
        # Greedy choice with slight randomness
        # Pick from the top 3 candidates
        idx = min(random.randint(0, 2), len(candidates) - 1)
        _, best_p, best_r, best_covered = candidates[idx]
        
        res_dict[best_p] = best_r
        uncovered -= best_covered
        used_primes.append(best_p)
        prod *= best_p**2
        
    if success and not uncovered:
        print(f"SUCCESS AT TRIAL {trial}!")
        print(f"used_primes = {used_primes}")
        print(f"res_dict = {res_dict}")
        print(f"prod = {prod} (digits: {len(str(prod))})")
        sys.stdout.flush()
        break

else:
    print("Failed to find a cover with 9 primes.")
