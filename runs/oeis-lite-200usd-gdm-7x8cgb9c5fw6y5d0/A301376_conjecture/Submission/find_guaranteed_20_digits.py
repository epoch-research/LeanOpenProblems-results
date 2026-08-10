import math
import sys
from sympy import isprime
from sympy.ntheory.modular import crt

X = 10**40  # $N$ will be around 10^20, which is well below 1.27 * 10^24

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

print("Generating V_all...", flush=True)
V_all = get_V_all(X)
print(f"Total V_all size: {len(V_all)}", flush=True)

# Precompute primes congruent to 3 mod 4
primes_3mod4 = [p for p in range(11, 2000) if isprime(p) and p % 4 == 3]

moduli = [9, 49]
residues = [1, 15]
res_dict = {3: 1, 7: 15}
used_primes = []

prod = 441
step = 1

while True:
    unblocked = []
    for v in V_all:
        blocked_by_some = False
        for p, r in res_dict.items():
            n2_mod_p2 = (r*r) % (p**2)
            val_mod_p2 = (n2_mod_p2 - v) % (p**2)
            if val_mod_p2 % p == 0 and val_mod_p2 != 0:
                blocked_by_some = True
                break
        if not blocked_by_some:
            unblocked.append(v)
            
    print(f"Step {step}: Currently unblocked count: {len(unblocked)}", flush=True)
    
    if len(unblocked) == 0:
        print("\nSUCCESS! ALL ELEMENTS BLOCKED!", flush=True)
        n, _ = crt(moduli, residues)
        n = int(n)
        if n % 2 == 0:
            n += prod
        print(f"n0 = {n}", flush=True)
        print(f"n0^2 = {n*n}", flush=True)
        print(f"used_primes = {used_primes}", flush=True)
        break
        
    best_p = None
    best_r = None
    best_blocked_count = -1
    
    available_primes = [p for p in primes_3mod4 if p not in res_dict]
    
    for p in available_primes[:30]:  # Check first 30 available primes
        roots_mod_p = set()
        for v in unblocked:
            v_mod_p = v % p
            if v_mod_p == 0:
                roots_mod_p.add(0)
            elif pow(v_mod_p, (p-1)//2, p) == 1:
                # Find square root
                for x in range(1, p):
                    if (x*x) % p == v_mod_p:
                        roots_mod_p.add(x)
                        roots_mod_p.add(p - x)
                        break
                        
        candidate_rs = []
        for r0 in roots_mod_p:
            for k in range(p):
                candidate_rs.append(r0 + k*p)
                
        for r in candidate_rs:
            blocked_count = 0
            n2_mod_p2 = (r*r) % (p**2)
            for v in unblocked:
                val_mod_p2 = (n2_mod_p2 - v) % (p**2)
                if val_mod_p2 % p == 0 and val_mod_p2 != 0:
                    blocked_count += 1
            if blocked_count > best_blocked_count:
                best_blocked_count = blocked_count
                best_p = p
                best_r = r
                
    print(f"Best prime to add: {best_p} with residue {best_r} (blocks {best_blocked_count} elements)", flush=True)
    moduli.append(best_p**2)
    residues.append(best_r)
    res_dict[best_p] = best_r
    used_primes.append((best_p, best_r))
    prod *= best_p**2
    step += 1
