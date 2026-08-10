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

# Primes pool congruent to 3 mod 4
primes_pool = [p for p in range(3, 1000) if isprime(p) and p % 4 == 3]

primes = [3, 7]
res_dict = {3: 1, 7: 15}
prod = 441 # product of squares of primes (3^2 * 7^2)

step = 1
while True:
    limit = prod**2
    V_all = get_V_all(limit)
    
    # Calculate currently unblocked
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
            
    print(f"Step {step}: prod = {prod} (digits: {len(str(prod))}), V_all size: {len(V_all)}, unblocked size: {len(unblocked)}")
    sys.stdout.flush()
    
    if len(unblocked) == 0:
        print("\nFOUND COMPLETE COVER!")
        print("Primes:", primes)
        print("Res dict:", res_dict)
        print("Prod:", prod)
        n, _ = crt([p**2 for p in primes], [res_dict[p] for p in primes])
        n = int(n)
        if n % 2 == 0:
            n += prod
        print("n0 =", n)
        print("n0^2 =", n*n)
        break
        
    if prod**2 >= 1.6 * 10**48:
        print("Exceeded limit!")
        break
        
    best_p = None
    best_r = None
    best_cov = -1
    
    for p in primes_pool:
        if p in res_dict:
            continue
        # Ensure we don't exceed the limit
        if prod * (p**2) >= 1.26 * 10**24:
            continue
            
        # We will count how many unblocked elements are blocked by each residue modulo p^2
        block_count = [0] * (p**2)
        
        # Precompute modular inverse of 2 modulo p
        inv2 = pow(2, p - 2, p)
        
        for v in unblocked:
            v_mod_p = v % p
            if v_mod_p == 0:
                if (v % (p**2)) != 0:
                    # All r = k * p for 0 <= k < p block v
                    for k in range(p):
                        block_count[k * p] += 1
            else:
                # Check if v is a QR modulo p
                if pow(v_mod_p, (p-1)//2, p) == 1:
                    # Find square roots modulo p
                    r0 = -1
                    for x in range(1, p):
                        if (x*x) % p == v_mod_p:
                            r0 = x
                            break
                    if r0 != -1:
                        roots = [r0, p - r0]
                        for rt in roots:
                            # Bad k satisfies: 2 * rt * k = (v - rt^2)/p mod p
                            d = (v - rt**2) // p
                            # k = d * (2 * rt)^-1 mod p
                            inv_2rt = pow(2 * rt, p - 2, p)
                            k_bad = (d * inv_2rt) % p
                            
                            # All k except k_bad block v
                            for k in range(p):
                                if k != k_bad:
                                    block_count[rt + k * p] += 1
                                    
        # Find the best residue r for this prime p
        max_cov = max(block_count)
        best_r_for_p = block_count.index(max_cov)
        
        if max_cov > best_cov:
            best_cov = max_cov
            best_p = p
            best_r = best_r_for_p
            
    if best_p is None or best_cov <= 0:
        print("No progress possible!")
        break
        
    primes.append(best_p)
    res_dict[best_p] = best_r
    prod *= best_p**2
    step += 1
