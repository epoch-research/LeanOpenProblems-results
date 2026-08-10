import math
import sys
from sympy import isprime
from sympy.ntheory.modular import crt

X = 10**20 # n0^2 will be around this, so n0 will be around 10^10 (10 digits)

def get_V_all(limit):
    V = [1]
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        if fs >= limit:
            break
        for i in range(160):
            val = fs * 4**i
            if val >= limit:
                break
            if val not in V:
                V.append(val)
    V.sort()
    return V

V_all = get_V_all(X)
print(f"Total V_all size: {len(V_all)}")
sys.stdout.flush()

# Keep primes under 350
primes_3mod4 = [p for p in range(11, 350) if isprime(p) and p % 4 == 3]

moduli = [9, 49]
residues = [1, 15]
res_dict = {3: 1, 7: 15}
used_primes = []

prod = 441

for step in range(1, 40):
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
            
    print(f"Step {step}: Currently unblocked count: {len(unblocked)}")
    sys.stdout.flush()
    
    if len(unblocked) == 0:
        print("SUCCESS! ALL ELEMENTS BLOCKED!")
        n, _ = crt(moduli, residues)
        n = int(n)
        if n % 2 == 0:
            n += prod
        print(f"n0 = {n}")
        print(f"n0^2 = {n*n}")
        print(f"used_primes = {used_primes}")
        break
        
    best_p = None
    best_r = None
    best_blocked_count = -1
    
    available_primes = [p for p in primes_3mod4 if p not in res_dict]
    if not available_primes:
        print("No more available primes under 350!")
        break
        
    for p in available_primes:
        roots_mod_p = set()
        for v in unblocked:
            v_mod_p = v % p
            if v_mod_p == 0:
                roots_mod_p.add(0)
            elif pow(v_mod_p, (p-1)//2, p) == 1:
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
                
    print(f"Best prime to add: {best_p} with residue {best_r} (blocks {best_blocked_count} elements)")
    sys.stdout.flush()
    moduli.append(best_p**2)
    residues.append(best_r)
    res_dict[best_p] = best_r
    used_primes.append((best_p, best_r))
    prod *= best_p**2
