import sys
import itertools
from sympy import isprime
from sympy.ntheory.modular import crt

V_all = [1, 4, 16, 26, 64, 104, 256, 314, 416, 1024, 1256, 1664, 4096, 4666, 5024, 6656]
primes_pool = [11, 19, 23, 31, 43, 47, 59, 67, 71, 79, 83]

# Backtracking search on a fixed set of primes
def check_combination(primes):
    # We want to find residues for primes to block all elements of V_all
    # We always include {3: 1, 7: 15}
    res_dict = {3: 1, 7: 15}
    
    # Calculate initial unblocked
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
            
    # Try to find residues for the chosen primes to block all of 'unblocked'
    # We can do this using a backtracking search on the residues of the chosen primes
    def dfs(idx, current_res_dict, current_unblocked):
        if len(current_unblocked) == 0:
            return current_res_dict
        if idx >= len(primes):
            return None
            
        p = primes[idx]
        # Find roots of current_unblocked mod p
        roots = set()
        for v in current_unblocked:
            v_mod_p = v % p
            if v_mod_p == 0:
                roots.add(0)
            elif pow(v_mod_p, (p-1)//2, p) == 1:
                for x in range(1, p):
                    if (x*x) % p == v_mod_p:
                        roots.add(x)
                        roots.add(p-x)
                        break
                        
        # Try all lifts of these roots mod p^2
        # To be fast, we sort lifts by how many elements they block
        lifts_with_counts = []
        for r0 in roots:
            for k in range(p):
                r = r0 + k*p
                # Count how many elements of current_unblocked are blocked
                count = 0
                n2_mod_p2 = r*r
                for v in current_unblocked:
                    val_mod_p2 = (n2_mod_p2 - v) % (p**2)
                    if val_mod_p2 % p == 0 and val_mod_p2 != 0:
                        count += 1
                if count > 0:
                    lifts_with_counts.append((count, r))
                    
        lifts_with_counts.sort(key=lambda x: x[0], reverse=True)
        
        for count, r in lifts_with_counts[:4]:
            new_res_dict = current_res_dict.copy()
            new_res_dict[p] = r
            new_unblocked = [v for v in current_unblocked if not ((r*r - v) % p == 0 and (r*r - v) % (p**2) != 0)]
            res = dfs(idx + 1, new_res_dict, new_unblocked)
            if res:
                return res
        return None

    return dfs(0, res_dict, unblocked)

print("Searching all combinations of 7 primes...")
for combo in itertools.combinations(primes_pool, 7):
    res = check_combination(combo)
    if res:
        print("\nSUCCESS! FOUND COVER!")
        print("Primes:", combo)
        print("Resdict:", res)
        # Solve CRT
        moduli = [p**2 for p in res]
        residues = [res[p] for p in res]
        n, prod = crt(moduli, residues)
        n = int(n)
        if n % 2 == 0:
            n += prod
        print("n0 =", n)
        print("n0^2 =", n*n)
        sys.exit(0)
        
print("No cover of size 7 found.")
