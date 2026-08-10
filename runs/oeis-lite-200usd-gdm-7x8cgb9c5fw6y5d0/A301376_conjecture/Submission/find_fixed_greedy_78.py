import sys
import math
from sympy import isprime
from sympy.ntheory.modular import crt

def get_V_all(limit):
    V = {1}
    for s in range(100):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        if fs >= limit:
            break
        for i in range(200):
            val = fs * 4**i
            if val >= limit:
                break
            V.add(val)
    return sorted(list(V))

limit = 10**78
V_all = get_V_all(limit)
print(f"Fixed limit: {limit}")
print(f"V_all size: {len(V_all)}")
sys.stdout.flush()

primes_pool = [p for p in range(3, 2000) if isprime(p) and p % 4 == 3]

primes = [3, 7]
res_dict = {3: 1, 7: 15}
unblocked = set(V_all)

# Remove elements blocked by 3 and 7
blocked_3_7 = set()
for v in unblocked:
    if (1 - v) % 3 == 0 and (1 - v) % 9 != 0:
        blocked_3_7.add(v)
    elif (225 - v) % 7 == 0 and (225 - v) % 49 != 0:
        blocked_3_7.add(v)
unblocked -= blocked_3_7
print(f"After 3 and 7: {len(unblocked)} elements left.")
sys.stdout.flush()

step = 3
while len(unblocked) > 0:
    best_p = None
    best_r = None
    best_cov = -1
    best_blocked = set()
    
    for p in primes_pool:
        if p in res_dict:
            continue
            
        block_count = [0] * (p**2)
        
        # Precompute square roots mod p
        sqrt_mod = [-1] * p
        for x in range(1, (p // 2) + 1):
            sqrt_mod[(x*x) % p] = x
            
        # Precompute modular inverses mod p
        inv_mod = [0] * p
        for x in range(1, p):
            inv_mod[x] = pow(x, p - 2, p)
            
        for v in unblocked:
            v_mod_p = v % p
            if v_mod_p == 0:
                if (v % (p**2)) != 0:
                    for k in range(p):
                        r = k * p
                        block_count[r] += 1
            else:
                r0 = sqrt_mod[v_mod_p]
                if r0 != -1:
                    r0_sq = r0 * r0
                    roots = [r0, p - r0]
                    for rt in roots:
                        d = (v - r0_sq) // p
                        inv_2rt = inv_mod[(2 * rt) % p]
                        k_bad = (d * inv_2rt) % p
                        for k in range(p):
                            if k != k_bad:
                                r = rt + k * p
                                block_count[r] += 1
                                    
        max_cov = max(block_count)
        best_r_for_p = block_count.index(max_cov)
        
        if max_cov > best_cov:
            best_cov = max_cov
            best_p = p
            best_r = best_r_for_p
            
    if best_p is None or best_cov <= 0:
        print("No progress possible!")
        break
        
    # Reconstruct the blocked set for the best (p, r)
    best_blocked = set()
    for v in unblocked:
        v_mod_p = v % best_p
        if v_mod_p == 0:
            if (v % (best_p**2)) != 0:
                if (best_r % best_p) == 0:
                    best_blocked.add(v)
        else:
            if (best_r * best_r - v) % best_p == 0 and (best_r * best_r - v) % (best_p**2) != 0:
                best_blocked.add(v)
                
    primes.append(best_p)
    res_dict[best_p] = best_r
    unblocked -= best_blocked
    print(f"Step {step}: Added p={best_p}, r={best_r} (blocked {best_cov} elements). Remaining: {len(unblocked)}")
    sys.stdout.flush()
    step += 1

if len(unblocked) == 0:
    print("\nFOUND COMPLETE COVER!")
    print("Primes:", primes)
    print("Res dict:", res_dict)
    n, prod = crt([p**2 for p in primes], [res_dict[p] for p in primes])
    n = int(n)
    prod = int(prod)
    if n % 2 == 0:
        n += prod
    print("n0 =", n)
    print("prod =", prod)
    print("n0 digits:", len(str(n)))
    print("prod digits:", len(str(prod)))
