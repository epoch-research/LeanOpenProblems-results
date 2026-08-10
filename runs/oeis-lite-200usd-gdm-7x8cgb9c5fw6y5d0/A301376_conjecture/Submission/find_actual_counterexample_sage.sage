import sys
import time

def is_sum_of_two_squares_exact(n):
    if n < 0: return False
    if n == 0 or n == 1: return True
    factors = factor(n)
    for p, exp in factors:
        if p % 4 == 3 and exp % 2 != 0:
            return False
    return True

def get_V_all_correct(limit):
    V = {1}
    for s in range(50):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        if fs >= limit:
            break
        for i in range(100):
            val = fs * 4**i
            if val >= limit:
                break
            V.add(val)
    return sorted(list(V))

primes_pool = [p for p in prime_range(3, 1000) if p % 4 == 3]

primes = [3, 7]
res_dict = {3: 1, 7: 15}
prod = 441

for step in range(1, 25):
    # Solve CRT to find N for this step
    moduli = [p**2 for p in primes]
    residues = [res_dict[p] for p in primes]
    n0 = int(crt(residues, moduli))
    pr_sq = prod**2
    if n0 % 2 == 0:
        n0 += pr_sq
        
    print(f"Step {step}: Base primes = {primes}, N = {n0} (digits: {len(str(n0))})")
    sys.stdout.flush()
    
    # Ensure N < 1.27 * 10^24
    if n0 >= 1.27 * 10**24:
        print("N exceeded the limit of 1.27 * 10^24! Failed.")
        break
        
    N2 = n0**2
    V_all_N = get_V_all_correct(N2)
    
    # Check if N has any solution
    has_sol = False
    failing_vs = []
    for v in V_all_N:
        diff = N2 - v
        if is_sum_of_two_squares_exact(diff):
            has_sol = True
            failing_vs.append(v)
            
    print(f"  V_all size: {len(V_all_N)}, Unblocked (has sol): {len(failing_vs)}")
    sys.stdout.flush()
    
    if not has_sol:
        print(f"\nSUCCESS!!! FOUND TRUE COUNTEREXAMPLE N = {n0}")
        print(f"N^2 = {N2}")
        print(f"Base primes = {primes}")
        print(f"V_all size = {len(V_all_N)}")
        sys.stdout.flush()
        
        # Find a blocking prime for each v in V_all_N
        blocking_primes = {}
        for v in V_all_N:
            diff = N2 - v
            factors = factor(diff)
            for p, exp in factors:
                if p % 4 == 3 and exp % 2 != 0:
                    blocking_primes[v] = int(p)
                    break
                    
        print(f"Number of distinct blocking primes used: {len(set(blocking_primes.values()))}")
        with open("/workspace/leanproject/Submission/success_exact.py", "w") as f:
            f.write(f"N = {n0}\n")
            f.write(f"blocking_primes = {blocking_primes}\n")
        break
        
    # Choose next best prime for greedy search on unblocked elements mod prod^2
    limit = prod**2
    V_all_unblocked = get_V_all_correct(limit)
    unblocked = []
    for v in V_all_unblocked:
        blocked = False
        for p, r in res_dict.items():
            n2_mod_p2 = (r*r) % (p**2)
            val_mod_p2 = (n2_mod_p2 - v) % (p**2)
            if val_mod_p2 % p == 0 and val_mod_p2 != 0:
                blocked = True
                break
        if not blocked:
            unblocked.append(v)
            
    best_p = None
    best_r = None
    best_cov = -1
    for p in primes_pool:
        if p in res_dict:
            continue
        block_count = [0] * (p**2)
        for v in unblocked:
            v_mod_p = v % p
            if v_mod_p == 0:
                if (v % (p**2)) != 0:
                    for k_idx in range(p):
                        block_count[k_idx * p] += 1
            else:
                if pow(v_mod_p, (p-1)//2, p) == 1:
                    r0 = -1
                    for x in range(1, p):
                        if (x*x) % p == v_mod_p:
                            r0 = x
                            break
                    if r0 != -1:
                        roots = [r0, p - r0]
                        for rt in roots:
                            d = (v - rt**2) // p
                            inv_2rt = pow(2 * rt, p - 2, p)
                            k_bad = (d * inv_2rt) % p
                            for k_idx in range(p):
                                if k_idx != k_bad:
                                    block_count[rt + k_idx * p] += 1
        max_cov = max(block_count)
        best_r_for_p = block_count.index(max_cov)
        if max_cov > best_cov:
            best_cov = max_cov
            best_p = p
            best_r = best_r_for_p
            
    primes.append(best_p)
    res_dict[best_p] = best_r
    prod *= best_p
