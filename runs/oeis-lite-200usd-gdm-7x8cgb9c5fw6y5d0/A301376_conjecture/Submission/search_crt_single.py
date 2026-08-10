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

# Primes congruent to 3 mod 4
prime_pool = [p for p in range(3, 500) if isprime(p) and p % 4 == 3]

# We will greedily select primes and their residues modulo p
primes = [3, 7]
res_dict = {3: 1, 7: 3} # N mod p, so N^2 mod p is r^2 mod p.
# For p=3: r=1, r^2=1 mod 3.
# For p=7: r=3, r^2=2 mod 7.
prod = 21

for step in range(1, 15):
    limit = prod**2
    V_all = get_V_all(limit)
    
    # Check which elements of V_all are guaranteed to be blocked by our current CRT base
    # An element v is blocked by p if v % p == r^2 % p and v % p^2 != r^2 % p^2?
    # Wait, we only know N mod p, so N = q * p + r.
    # N^2 = q^2 * p^2 + 2 * q * p * r + r^2.
    # So N^2 mod p^2 = (2 * q * p * r + r^2) % p^2.
    # This depends on q! So it is NOT fixed by N mod p alone.
    # BUT wait! If v % p == r^2 % p, then N^2 - v is always divisible by p!
    # And the probability that p^2 divides N^2 - v is only 1/p.
    # So we can't GUARANTEE the block, but we can say that v is "highly likely to be blocked" by p.
    # Actually, for greedy search, we can just assume v is blocked if v % p == r^2 % p,
    # and then check the candidates N = n_base + k * prod.
    
    unblocked = []
    for v in V_all:
        blocked = False
        for p, r in res_dict.items():
            r2 = (r*r) % p
            if v % p == r2:
                blocked = True
                break
        if not blocked:
            unblocked.append(v)
            
    print(f"Step {step}: Primes = {primes}, prod = {prod} (digits: {len(str(prod))}), V_all = {len(V_all)}, Unblocked = {len(unblocked)}")
    sys.stdout.flush()
    
    if len(unblocked) == 0:
        print("\nSUCCESS! ALL ELEMENTS DESIGNED TO BE BLOCKED!")
        break
        
    # Choose next best prime to block the most unblocked elements
    best_p = None
    best_r = None
    best_cov = -1
    for p in prime_pool:
        if p in res_dict:
            continue
            
        # For each possible residue r mod p, count how many unblocked elements are congruent to r^2 mod p
        cov_for_r = [0] * p
        for v in unblocked:
            v_mod = v % p
            # We want to find x mod p such that x^2 == v_mod mod p
            if v_mod == 0:
                cov_for_r[0] += 1
            elif pow(v_mod, (p-1)//2, p) == 1:
                # Find the square roots of v_mod
                for x in range(1, p):
                    if (x*x) % p == v_mod:
                        cov_for_r[x] += 1
                        cov_for_r[p - x] += 1
                        break
        max_cov = max(cov_for_r)
        best_r_for_p = cov_for_r.index(max_cov)
        
        if max_cov > best_cov:
            best_cov = max_cov
            best_p = p
            best_r = best_r_for_p
            
    if best_p is None or best_cov == 0:
        print("No more primes can block any elements!")
        break
        
    primes.append(best_p)
    res_dict[best_p] = best_r
    prod *= best_p
