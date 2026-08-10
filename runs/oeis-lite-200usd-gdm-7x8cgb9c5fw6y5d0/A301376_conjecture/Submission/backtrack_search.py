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

primes_pool = [p for p in range(3, 100) if isprime(p) and p % 4 == 3]
print(f"Primes pool: {primes_pool}")

# We will do a depth-first search
# State: (current_moduli, current_residues, current_prod)
best_unblocked = 999999

def search(depth, moduli, residues, prod, res_dict):
    global best_unblocked
    
    limit = prod**2
    V_all = get_V_all(limit)
    
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
            
    unblocked_count = len(unblocked)
    if unblocked_count < best_unblocked:
        best_unblocked = unblocked_count
        print(f"New best unblocked count: {unblocked_count} at depth {depth}, prod={prod} (digits: {len(str(prod))})")
        sys.stdout.flush()
        
    if unblocked_count == 0:
        print("\nSUCCESS! FOUND PERFECT COMBINATION!")
        n, _ = crt(moduli, residues)
        n = int(n)
        if n % 2 == 0:
            n += prod
        print(f"N = {n}")
        print(f"N^2 = {n*n}")
        print(f"moduli = {moduli}")
        print(f"residues = {residues}")
        sys.exit(0)
        
    if prod >= 1.27 * 10**12: # prod^2 < 1.6 * 10^24
        return
        
    # Choose next prime
    # To be smart, we sort available primes by how many elements they can block
    available_primes = [p for p in primes_pool if p not in res_dict]
    if not available_primes:
        return
        
    prime_candidates = []
    for p in available_primes:
        # Find roots mod p for the unblocked elements
        roots_mod_p = set()
        for v in unblocked:
            v_mod_p = v % p
            if v_mod_p == 0:
                roots_mod_p.add(0)
            elif pow(v_mod_p, (p-1)//2, p) == 1:
                for r0 in range(1, p):
                    if (r0*r0) % p == v_mod_p:
                        roots_mod_p.add(r0)
                        roots_mod_p.add(p - r0)
                        break
        if not roots_mod_p:
            continue
            
        # For each root, try all lifts mod p^2
        for r0 in roots_mod_p:
            for k in range(p):
                r = r0 + k*p
                # Count blocked
                blocked_count = 0
                n2_mod_p2 = (r*r) % (p**2)
                for v in unblocked:
                    val_mod_p2 = (n2_mod_p2 - v) % (p**2)
                    if val_mod_p2 % p == 0 and val_mod_p2 != 0:
                        blocked_count += 1
                if blocked_count > 0:
                    prime_candidates.append((blocked_count, p, r))
                    
    # Sort candidates by blocked_count descending
    prime_candidates.sort(key=lambda x: x[0], reverse=True)
    
    # Try the top candidates
    for blocked_count, p, r in prime_candidates[:5]:
        new_moduli = moduli + [p**2]
        new_residues = residues + [r]
        new_res_dict = res_dict.copy()
        new_res_dict[p] = r
        search(depth + 1, new_moduli, new_residues, prod * (p**2), new_res_dict)

search(0, [9, 49], [1, 15], 441, {3: 1, 7: 15})
print("Search finished without success.")
