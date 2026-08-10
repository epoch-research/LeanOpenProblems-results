import sys
import math
from collections import defaultdict
from sympy import isprime, factorint
from sympy.ntheory.modular import crt

def is_sum_of_two_squares_exact(n):
    if n < 0: return False
    if n == 0 or n == 1: return True
    factors = factorint(n)
    for p, exp in factors.items():
        if p % 4 == 3 and exp % 2 != 0:
            return False
    return True

def get_V_all_correct(limit):
    V = {1}
    for s in range(50):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        if fs >= limit:
            break
        for i in range(100):
            val = fs * 4**i
            if val >= limit:
                break
            V.add(val)
    return sorted(list(V))

primes_pool = [p for p in range(3, 20000) if isprime(p) and p % 4 == 3]

# Start with {3, 7} as in the original
primes = [3, 7]
res_dict = {3: 1, 7: 15}
prod = 441

for step in range(1, 100):
    # Solve CRT to find N for this step
    moduli = [p**2 for p in primes]
    residues = [res_dict[p] for p in primes]
    n0, pr_sq = crt(moduli, residues)
    n0 = int(n0)
    if n0 % 2 == 0:
        n0 += pr_sq
        
    N2 = n0**2
    V_all_N = get_V_all_correct(N2)
    
    # Check if N has any solution
    failing_vs = []
    for v in V_all_N:
        diff = N2 - v
        if is_sum_of_two_squares_exact(diff):
            failing_vs.append(v)
            
    print(f"Step {step}: Prod digits: {len(str(prod))}, V_all size: {len(V_all_N)}, Unblocked (has sol): {len(failing_vs)}")
    sys.stdout.flush()
    
    if len(failing_vs) == 0:
        print(f"\nSUCCESS!!! FOUND TRUE COUNTEREXAMPLE N = {n0}")
        print(f"N^2 = {N2}")
        print(f"Base primes = {primes}")
        print(f"V_all size = {len(V_all_N)}")
        sys.stdout.flush()
        
        # Find a blocking prime for each v in V_all_N
        blocking_primes = {}
        for v in V_all_N:
            diff = N2 - v
            factors = factorint(diff)
            for p, exp in factors.items():
                if p % 4 == 3 and exp % 2 != 0:
                    blocking_primes[v] = int(p)
                    break
        print(f"Blocking primes size: {len(blocking_primes)}")
        with open("/workspace/leanproject/Submission/success_exact.py", "w") as f:
            f.write(f"N = {n0}\n")
            f.write(f"blocking_primes = {blocking_primes}\n")
        break
        
    # Choose next best prime to add from primes_pool using our fast O(log p) algorithm on unblocked elements
    unblocked = failing_vs
    best_p = None
    best_r = None
    best_covered = set()
    best_score = -1
    
    for p in primes_pool:
        if p in res_dict:
            continue
            
        by_mod_p = defaultdict(list)
        for v in unblocked:
            by_mod_p[v % p].append(v)
            
        allowed_r_mod_p = set()
        for vp in by_mod_p.keys():
            if vp == 0:
                allowed_r_mod_p.add(0)
            elif pow(vp, (p-1)//2, p) == 1:
                r0 = pow(vp, (p+1)//4, p)
                allowed_r_mod_p.add(r0)
                allowed_r_mod_p.add(p-r0)
                        
        if not allowed_r_mod_p:
            continue
            
        best_p_r = None
        best_p_covered = set()
        
        for r0 in allowed_r_mod_p:
            r2_mod_p = (r0 * r0) % p
            candidates_v = by_mod_p[r2_mod_p]
            if not candidates_v:
                continue
                
            # By Hensel's lemma, lift r0 to mod p^2
            if r0 == 0:
                covered_blocked = set(v for v in candidates_v if (v % (p**2)) != 0)
                if len(covered_blocked) > len(best_p_covered):
                    best_p_covered = covered_blocked
                    best_p_r = 0
            else:
                diff = (vp - r0*r0) // p
                inv_2r0 = pow(2*r0, p-2, p)
                k1 = (diff * inv_2r0) % p
                r1 = (r0 + k1*p) % (p**2)
                
                r0_neg = p - r0
                diff_neg = (vp - r0_neg*r0_neg) // p
                inv_2r0_neg = pow(2*r0_neg, p-2, p)
                k_neg = (diff_neg * inv_2r0_neg) % p
                r2 = (r0_neg + k_neg*p) % (p**2)
                
                for r in [r1, r2]:
                    r2_mod_p2 = (r * r) % (p**2)
                    covered_blocked = set(v for v in candidates_v if (v % (p**2)) != r2_mod_p2)
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
        print("Failed to find any prime to cover remaining elements.")
        break
        
    primes.append(best_p)
    res_dict[best_p] = best_r
    prod *= best_p**2
