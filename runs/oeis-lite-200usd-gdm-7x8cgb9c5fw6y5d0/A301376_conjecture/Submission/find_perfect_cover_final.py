import math
import sys
from collections import defaultdict
from sympy import isprime
from sympy.ntheory.modular import crt

def get_V_all_correct(limit):
    V = {1}
    for s in range(105):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        if fs >= limit:
            break
        for i in range(210):
            val = fs * 4**i
            if val >= limit:
                break
            V.add(val)
    return sorted(list(V))

limit = 10**125
V_all = get_V_all_correct(limit)
print(f"V_all size for limit {limit}: {len(V_all)}")
sys.stdout.flush()

primes_pool = [p for p in range(11, 2000) if isprime(p) and p % 4 == 3]

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
sys.stdout.flush()

step = 1
while uncovered:
    best_p = None
    best_r = None
    best_covered = set()
    best_score = -1
    
    # We restrict to first 25 available primes
    available_primes = [p for p in primes_pool if p not in res_dict and prod * (p**2) < 10**62]
    for p in available_primes[:25]:
            
        # Group uncovered by v % p
        by_mod_p = defaultdict(list)
        for v in uncovered:
            by_mod_p[v % p].append(v)
            
        allowed_r_mod_p = set()
        for vp in by_mod_p.keys():
            if vp == 0:
                allowed_r_mod_p.add(0)
            elif pow(vp, (p-1)//2, p) == 1:
                # Find square root mod p
                for x in range(1, p):
                    if (x*x) % p == vp:
                        allowed_r_mod_p.add(x)
                        allowed_r_mod_p.add(p-x)
                        break
                        
        if not allowed_r_mod_p:
            continue
            
        best_p_r = None
        best_p_covered = set()
        
        for r0 in allowed_r_mod_p:
            r2_mod_p = (r0 * r0) % p
            candidates_v = by_mod_p[r2_mod_p]
            if not candidates_v:
                continue
                
            for k in range(p):
                r = r0 + k * p
                r2_mod_p2 = (r * r) % (p**2)
                
                covered_blocked = set()
                for v in candidates_v:
                    if (v % (p**2)) != r2_mod_p2:
                        covered_blocked.add(v)
                        
                if len(covered_blocked) > len(best_p_covered):
                    best_p_covered = covered_blocked
                    best_p_r = r
                    
        if len(best_p_covered) > 0:
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
    print(f"Step {step}: Added p={best_p}, r={best_r} (covers {len(best_covered)}). Uncovered remaining: {len(uncovered)}. Current prod digits: {len(str(prod))}")
    sys.stdout.flush()
    step += 1

if not uncovered:
    print("\nSUCCESS!")
    moduli = [p**2 for p in used_primes]
    residues = [res_dict[p] for p in used_primes]
    n, prod = crt(moduli, residues)
    n = int(n)
    if n % 2 == 0:
        n += prod
    print(f"n0 = {n}")
    print(f"n0_sq = {n*n}")
    print(f"used_primes = {used_primes}")
    print(f"res_dict = {res_dict}")
    sys.stdout.flush()
    with open("/workspace/leanproject/Submission/final_optimal_result.txt", "w") as f:
        f.write(f"n0 = {n}\n")
        f.write(f"used_primes = {used_primes}\n")
        f.write(f"res_dict = {res_dict}\n")
