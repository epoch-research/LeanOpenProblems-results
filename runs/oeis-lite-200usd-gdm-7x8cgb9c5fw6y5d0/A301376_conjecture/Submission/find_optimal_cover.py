import sys
from sympy import isprime
from sympy.ntheory.modular import crt

V_all = [1, 4, 16, 26, 64, 104, 256, 314, 416, 1024, 1256, 1664, 4096, 4666, 5024, 6656]
primes_pool = [p for p in range(11, 200) if isprime(p) and p % 4 == 3]

def search(depth, moduli, residues, prod, res_dict):
    # Calculate unblocked
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
            
    if len(unblocked) == 0:
        print("\nSUCCESS! FOUND OPTIMAL COVER!")
        print("used_primes =", list(res_dict.items()))
        n, _ = crt(moduli, residues)
        n = int(n)
        if n % 2 == 0:
            n += prod
        print("n0 =", n)
        print("n0_sq =", n*n)
        sys.exit(0)
        
    if depth >= 7: # We only allow up to 7 extra primes (so 9 total primes including 3 and 7)
        return
        
    # Try adding a prime from primes_pool
    for p in primes_pool:
        if p in res_dict:
            continue
            
        # Find all roots of unblocked elements mod p
        roots = set()
        for v in unblocked:
            v_mod_p = v % p
            if v_mod_p == 0:
                roots.add(0)
            elif pow(v_mod_p, (p-1)//2, p) == 1:
                for x in range(1, p):
                    if (x*x) % p == v_mod_p:
                        roots.add(x)
                        roots.add(p-x)
                        break
                        
        # For each root, try all p lifts
        for r0 in roots:
            for k in range(p):
                r = r0 + k*p
                # Check if this r blocks at least one unblocked element
                blocks_any = False
                n2_mod_p2 = r*r
                for v in unblocked:
                    val_mod_p2 = (n2_mod_p2 - v) % (p**2)
                    if val_mod_p2 % p == 0 and val_mod_p2 != 0:
                        blocks_any = True
                        break
                if blocks_any:
                    new_moduli = moduli + [p**2]
                    new_residues = residues + [r]
                    new_res_dict = res_dict.copy()
                    new_res_dict[p] = r
                    search(depth + 1, new_moduli, new_residues, prod * p**2, new_res_dict)

# Start search with {3: 1, 7: 15}
search(0, [9, 49], [1, 15], 441, {3: 1, 7: 15})
print("Search finished.")
