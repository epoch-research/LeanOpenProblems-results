import sys
import itertools
from sympy import isprime
from sympy.ntheory.modular import crt

blocked_targets = [26, 104, 314, 416, 1256, 1664, 5024, 6656, 20096, 26624, 73274, 80384]
primes_pool = [p for p in range(11, 200) if isprime(p) and p % 4 == 3]

# We want to find a subset of primes and residues of minimal product that blocks all 12 targets
# Since we only have 12 targets, maybe 4 or 5 primes are enough!
# Let's search all subsets of primes_pool of size 4 and 5
print("Searching for a subset of size 4...")
for combo in itertools.combinations(primes_pool, 4):
    # We also include 3 and 7
    res_dict = {3: 1, 7: 15}
    unblocked = set(blocked_targets)
    # 3 and 7 don't block any of these 12 targets because they are not congruent to square roots mod p, or they are?
    # Let's check
    blocked_3_7 = set()
    for v in unblocked:
        blocked = False
        for p, r in res_dict.items():
            n2_mod_p2 = (r*r) % (p**2)
            val_mod_p2 = (n2_mod_p2 - v) % (p**2)
            if val_mod_p2 % p == 0 and val_mod_p2 != 0:
                blocked = True
                break
        if blocked:
            blocked_3_7.add(v)
    uncovered = unblocked - blocked_3_7
    
    # Now backtracking on 'combo' to cover 'uncovered'
    primes = list(combo)
    def dfs(idx, current_res_dict, current_uncovered):
        if len(current_uncovered) == 0:
            return current_res_dict
        if idx >= len(primes):
            return None
        p = primes[idx]
        roots = set()
        for v in current_uncovered:
            v_mod_p = v % p
            if v_mod_p == 0:
                roots.add(0)
            elif pow(v_mod_p, (p-1)//2, p) == 1:
                for x in range(1, p):
                    if (x*x) % p == v_mod_p:
                        roots.add(x)
                        roots.add(p-x)
                        break
        for r0 in roots:
            for k in range(p):
                r = r0 + k*p
                covered = set(v for v in current_uncovered if (r*r - v) % p == 0 and (r*r - v) % (p**2) != 0)
                if len(covered) > 0:
                    new_res_dict = current_res_dict.copy()
                    new_res_dict[p] = r
                    res = dfs(idx + 1, new_res_dict, current_uncovered - covered)
                    if res:
                        return res
        return None
        
    res = dfs(0, res_dict, uncovered)
    if res:
        print("\nSUCCESS! FOUND COVER OF SIZE 4!")
        print("Primes:", combo)
        print("Resdict:", res)
        moduli = [p**2 for p in res]
        residues = [res[p] for p in res]
        n, prod = crt(moduli, residues)
        n = int(n)
        if n % 2 == 0:
            n += prod
        print("n0 =", n)
        sys.exit(0)
        
print("No cover of size 4 found.")
