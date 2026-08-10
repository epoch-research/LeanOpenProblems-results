import math
import sys
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

# Limit chosen to be 10**48 (so N <= 10**24)
limit = 10**48
V_all = get_V_all(limit)
print(f"V_all size for limit {limit}: {len(V_all)}")

# Primes congruents to 3 mod 4
primes_pool = [p for p in range(11, 20000) if isprime(p) and p % 4 == 3]

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

while uncovered:
    best_p = None
    best_r = None
    best_covered = set()
    best_score = -1
    
    for p in primes_pool:
        if p in res_dict:
            continue
            
        # Group uncovered by v % p
        by_mod_p = defaultdict(list)
        for v in uncovered:
            by_mod_p[v % p].append(v)
            
        # We want to find a residue r mod p^2 such that r^2 mod p^2 blocks as many elements as possible.
        # For a fixed v_mod_p (where vp % p == r^2 % p):
        # We want r^2 % p^2 to not match v % p^2.
        # Since r^2 % p = v_mod_p, we can find the square roots of v_mod_p mod p.
        # Let them be r0 and p - r0.
        # By Hensel's lemma, each of r0 and p-r0 lifts to a unique square root mod p^2.
        # Let's find these two lifts mod p^2.
        # Their squares mod p^2 will be the only two possible values of r^2 mod p^2 congruent to v_mod_p mod p.
        # We check which of these two values minimizes the match with v % p^2.
        
        for vp, candidates_v in by_mod_p.items():
            if vp == 0:
                # r0 = 0. Its only lift is 0. So r^2 % p^2 = 0.
                # Any v in candidates_v with v % p^2 != 0 is blocked.
                covered_blocked = set(v for v in candidates_v if (v % (p**2)) != 0)
                score = len(covered_blocked) / math.log(p**2)
                if score > best_score:
                    best_score = score
                    best_p = p
                    best_r = 0
                    best_covered = covered_blocked
            elif pow(vp, (p-1)//2, p) == 1:
                # find a square root r0 mod p
                r0 = pow(vp, (p+1)//4, p)
                
                # Lift r0 to mod p^2
                # We want (r0 + k*p)^2 = r0^2 + 2*k*p*r0 = vp mod p^2
                # so 2*k*r0 = (vp - r0^2)/p mod p
                # k = (vp - r0^2)/p * (2*r0)^-1 mod p
                diff = (vp - r0*r0) // p
                inv_2r0 = pow(2*r0, p-2, p)
                k = (diff * inv_2r0) % p
                r1 = (r0 + k*p) % (p**2)
                
                # Similarly for p - r0
                r0_neg = p - r0
                diff_neg = (vp - r0_neg*r0_neg) // p
                inv_2r0_neg = pow(2*r0_neg, p-2, p)
                k_neg = (diff_neg * inv_2r0_neg) % p
                r2 = (r0_neg + k_neg*p) % (p**2)
                
                # Check both r1 and r2
                for r in [r1, r2]:
                    r2_mod_p2 = (r * r) % (p**2)
                    covered_blocked = set(v for v in candidates_v if (v % (p**2)) != r2_mod_p2)
                    score = len(covered_blocked) / math.log(p**2)
                    if score > best_score:
                        best_score = score
                        best_p = p
                        best_r = r
                        best_covered = covered_blocked
                        
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
    print(f"n0_sq = {n*n}")
    print(f"used_primes = {used_primes}")
    print(f"res_dict = {res_dict}")
