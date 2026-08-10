import sys
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

primes_3mod4 = [p for p in range(11, 200) if isprime(p) and p % 4 == 3]

def solve():
    # We want to find a cover of V_all(prod**2) using a subset of primes_3mod4
    # such that the subset size is at most 6.
    # Let's do a backtracking search on the subset of primes.
    best_size = 99
    
    # We can do a depth-first search
    def dfs(used_primes, res_dict, prod, step):
        V_all = get_V_all(prod**2)
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
                
        if len(unblocked) == 0:
            print(f"FOUND COVER OF SIZE {len(used_primes)}!")
            print(f"prod = {prod} (digits: {len(str(prod))})")
            print("used_primes:", used_primes)
            n, _ = crt([9, 49] + [p**2 for p, _ in used_primes], [1, 15] + [r for _, r in used_primes])
            n = int(n)
            if n % 2 == 0:
                n += prod
            print(f"n0 = {n}")
            sys.exit(0)
            
        if len(used_primes) >= 6:
            return
            
        # Try adding another prime
        # To find the best prime, we can rank them by how many elements they can block
        candidates = []
        available_primes = [p for p in primes_3mod4 if p not in res_dict]
        for p in available_primes:
            # Skip if prod exceeds limit
            if prod * (p**2) >= 1.27 * 10**24:
                continue
                
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
                            
            best_r = None
            best_blocked = 0
            for r0 in roots_mod_p:
                for k in range(p):
                    r = r0 + k*p
                    blocked_count = 0
                    n2_mod_p2 = (r*r) % (p**2)
                    for v in unblocked:
                        val_mod_p2 = (n2_mod_p2 - v) % (p**2)
                        if val_mod_p2 % p == 0 and val_mod_p2 != 0:
                            blocked_count += 1
                    if blocked_count > best_blocked:
                        best_blocked = blocked_count
                        best_r = r
                        
            if best_blocked > 0:
                candidates.append((best_blocked, p, best_r))
                
        # Sort candidates descending by blocked count
        candidates.sort(reverse=True)
        
        for blocked_count, p, r in candidates[:3]: # try the top 3 best primes
            res_dict[p] = r
            dfs(used_primes + [(p, r)], res_dict, prod * (p**2), step + 1)
            del res_dict[p]

    res_dict = {3: 1, 7: 15}
    dfs([], res_dict, 441, 1)

solve()
