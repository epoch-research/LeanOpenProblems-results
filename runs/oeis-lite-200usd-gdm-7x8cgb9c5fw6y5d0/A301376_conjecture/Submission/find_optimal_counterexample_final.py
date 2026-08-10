import math
import sys
from sympy import isprime
from sympy.ntheory.modular import crt

def get_V_all_correct(limit):
    V = {1}
    if limit > 10:
        max_s = int(math.log(limit * 9 / 10, 16)) + 5
    else:
        max_s = 5
    for s in range(max_s):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        if fs >= limit:
            break
        max_i = int(math.log(limit / fs, 4)) + 5
        for i in range(max_i):
            val = fs * 4**i
            if val >= limit:
                break
            V.add(val)
    return sorted(list(V))

# Primes pool congruent to 3 mod 4 under 2000
primes_3mod4 = [p for p in range(11, 2000) if isprime(p) and p % 4 == 3]

moduli = [9, 49]
residues = [1, 15]
res_dict = {3: 1, 7: 15}
used_primes = []

prod = 441
step = 1

while True:
    limit = prod**2
    V_all = get_V_all_correct(limit)
    
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
            
    print(f"Step {step}: Prod = {prod} (digits: {len(str(prod))}), V_all size: {len(V_all)}, Unblocked: {len(unblocked)}")
    sys.stdout.flush()
    
    if len(unblocked) == 0:
        print("\nSUCCESS! ALL ELEMENTS BLOCKED!")
        n, _ = crt(moduli, residues)
        n = int(n)
        if n % 2 == 0:
            n += prod
        print(f"n0 = {n}")
        print(f"n0_sq = {n*n}")
        print(f"used_primes = {used_primes}")
        sys.stdout.flush()
        with open("/workspace/leanproject/Submission/final_optimal_result.txt", "w") as f:
            f.write(f"n0 = {n}\n")
            f.write(f"used_primes = {used_primes}\n")
        break
        
    best_p = None
    best_r = None
    best_blocked_count = -1
    
    available_primes = [p for p in primes_3mod4 if p not in res_dict]
    if not available_primes:
        print("No more available primes!")
        break
        
    # Check candidates (only the first 3 available primes to be super fast!)
    for p in available_primes[:3]:
        roots_mod_p = set()
        for v in unblocked:
            v_mod_p = v % p
            if v_mod_p == 0:
                roots_mod_p.add(0)
            elif pow(v_mod_p, (p-1)//2, p) == 1:
                # Find square root mod p
                for x in range(1, p):
                    if (x*x) % p == v_mod_p:
                        roots_mod_p.add(x)
                        roots_mod_p.add(p-x)
                        break
                        
        candidate_rs = []
        for r0 in roots_mod_p:
            for k in range(p):
                candidate_rs.append(r0 + k*p)
                
        for r in candidate_rs:
            blocked_count = 0
            n2_mod_p2 = r*r
            for v in unblocked:
                val_mod_p2 = (n2_mod_p2 - v) % (p**2)
                if val_mod_p2 % p == 0 and val_mod_p2 != 0:
                    blocked_count += 1
            if blocked_count > best_blocked_count:
                best_blocked_count = blocked_count
                best_p = p
                best_r = r
                
    if best_p is None or best_blocked_count <= 0:
        print("Failed to find any prime to cover remaining elements.")
        break
        
    moduli.append(best_p**2)
    residues.append(best_r)
    res_dict[best_p] = best_r
    used_primes.append((best_p, best_r))
    prod *= best_p**2
    step += 1
