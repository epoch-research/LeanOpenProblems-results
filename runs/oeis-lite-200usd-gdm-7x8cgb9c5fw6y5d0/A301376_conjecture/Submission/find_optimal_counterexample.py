import math
import sys
from sympy import isprime
from sympy.ntheory.modular import crt

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

# Precompute primes congruent to 3 mod 4
primes_3mod4 = [p for p in range(11, 2000) if isprime(p) and p % 4 == 3]

# We start with moduli 9 and 49, and residues 1 and 15
moduli = [9, 49]
residues = [1, 15]

# Current product of moduli
prod = 441

# We will greedily add primes
used_primes = []

for step in range(1, 40):
    print(f"\n--- Step {step} ---")
    print(f"Current prod: {prod} (digits: {len(str(prod))})")
    
    # Generate V_all up to prod^2 (which is the upper bound of n^2)
    # Actually, n < prod, so n^2 < prod^2.
    V_all = get_V_all(prod**2)
    print(f"V_all size: {len(V_all)}")
    
    # Find which elements of V_all are currently unblocked
    # An element v is blocked if for some prime p in {3, 7} + used_primes:
    # (n^2 - v) is divisible by p but not p^2.
    # Since we haven't determined n yet, we can't check this for the whole prod.
    # But for any v < prod^2, we can check if it is blocked by the already chosen residues!
    # Specifically, for each p in {3, 7} + used_primes, we know the residue of n mod p^2.
    # So we know the residue of n^2 - v mod p^2.
    # Thus we can check if (n^2 - v) is blocked by p!
    unblocked = []
    
    # We map each prime to its residue of n mod p^2
    res_dict = {3: 1, 7: 15}
    for p, r in used_primes:
        res_dict[p] = r
        
    for v in V_all:
        blocked_by_some = False
        for p, r in res_dict.items():
            # n^2 mod p^2 is r^2 mod p^2
            n2_mod_p2 = (r*r) % (p**2)
            val_mod_p2 = (n2_mod_p2 - v) % (p**2)
            if val_mod_p2 % p == 0 and val_mod_p2 != 0:
                blocked_by_some = True
                break
        if not blocked_by_some:
            unblocked.append(v)
            
    print(f"Currently unblocked count: {len(unblocked)}")
    if len(unblocked) == 0:
        print("SUCCESS! ALL ELEMENTS BLOCKED!")
        # Find n
        n, _ = crt(moduli, residues)
        n = int(n)
        if n % 2 == 0:
            n += prod
        print(f"n = {n}")
        print(f"n^2 = {n*n}")
        print(f"used_primes = {used_primes}")
        break
        
    # We want to choose the next prime p and its residue r mod p^2
    # to maximize the number of blocked elements from the `unblocked` list.
    best_p = None
    best_r = None
    best_blocked_count = -1
    
    # We only consider primes that haven't been used yet
    available_primes = [p for p in primes_3mod4 if p not in res_dict]
    
    # To keep it fast, we only test the first 20 available primes
    for p in available_primes[:20]:
        # Test all possible residues r mod p^2
        # Actually, r must be a square root mod p of some v % p for at least one v in unblocked?
        # Not necessarily, but n^2 mod p must be a QR mod p.
        # So r mod p can be any element in range(p).
        # And r mod p^2 = r_0 + k*p for k in range(p).
        # So there are p^2 possible residues r mod p^2.
        for r in range(p**2):
            # Check how many elements in `unblocked` would be blocked by (p, r)
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
    moduli.append(best_p**2)
    residues.append(best_r)
    used_primes.append((best_p, best_r))
    prod *= best_p**2
