import sys
import time

def precompute_V():
    V = {1}
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(160):
            val = fs * 4**i
            V.add(val)
    return sorted(list(V))

all_V = precompute_V()

def find_counterexample(num_primes):
    print(f"\n==========================================")
    print(f"Running search with {num_primes} primes...")
    
    # Primes pool
    primes_pool = [p for p in prime_range(3, 300) if p % 4 == 3]
    
    N_max = 10**8
    # Iterative optimization to match N_max with base_prod
    for iteration in range(5):
        limit = N_max * N_max
        V_target = [v for v in all_V if v < limit]
        
        selected_primes = []
        selected_residues = {}
        uncovered = list(V_target)
        
        for _ in range(num_primes):
            best_p = None
            best_r = None
            best_cov = -1
            
            for p in primes_pool:
                if p in selected_primes:
                    continue
                cov_for_r = [0] * p
                for v in uncovered:
                    v_mod = v % p
                    if v_mod == 0:
                        cov_for_r[0] += 1
                    elif pow(v_mod, (p-1)//2, p) == 1:
                        for r in range(1, p):
                            if (r*r) % p == v_mod:
                                cov_for_r[r] += 1
                                cov_for_r[p-r] += 1
                                break
                max_cov = max(cov_for_r)
                best_r_for_p = cov_for_r.index(max_cov)
                if max_cov > best_cov:
                    best_cov = max_cov
                    best_p = p
                    best_r = best_r_for_p
                    
            if best_cov <= 0:
                break
                
            selected_primes.append(best_p)
            selected_residues[best_p] = best_r
            new_uncovered = []
            r2 = (best_r * best_r) % best_p
            for v in uncovered:
                if v % best_p != r2:
                    new_uncovered.append(v)
            uncovered = new_uncovered
            
        moduli = [2] + selected_primes
        residues = [1] + [selected_residues[p] for p in selected_primes]
        from math import prod as math_prod
        base_prod = math_prod(moduli)
        
        # We want N_max to be at least 2 * base_prod to cover k=0 and k=1
        new_N_max = 2 * base_prod
        if abs(new_N_max - N_max) < 0.01 * N_max:
            # Converged!
            break
        N_max = new_N_max
        
    N0 = int(crt(residues, moduli))
    print(f"Converged after {iteration+1} iterations.")
    print(f"Selected Primes: {selected_primes}")
    print(f"Selected Residues: {[selected_residues[p] for p in selected_primes]}")
    print(f"CRT base: N0 = {N0}, prod = {base_prod}, digits = {len(str(base_prod))}")
    print(f"V_target size = {len(V_target)}, uncovered remaining = {len(uncovered)}")
    
    # Now check k = 0, 1, 2
    start_time = time.time()
    for k in range(5):
        N = N0 + k * base_prod
        if N <= 1:
            continue
        if N >= 1.27 * 10**24:
            break
            
        N2 = N * N
        V_actual = [v for v in all_V if v < N2]
        
        all_blocked = True
        blocking_primes = {}
        for v in V_actual:
            diff = N2 - v
            found_p = None
            for p in selected_primes:
                if diff % p == 0 and diff % (p*p) != 0:
                    found_p = p
                    break
            if found_p is None:
                factors = factor(diff)
                for p, exp in factors:
                    if p % 4 == 3 and exp % 2 != 0:
                        found_p = int(p)
                        break
            if found_p is not None:
                blocking_primes[v] = found_p
            else:
                all_blocked = False
                break
                
        if all_blocked:
            print(f"SUCCESS! Found N = {N} (k = {k}) in {time.time() - start_time:.2f}s")
            print(f"N^2 = {N2}")
            print(f"V_all size = {len(V_actual)}")
            print(f"blocking_primes = {blocking_primes}")
            return N, blocking_primes
            
    print("No counterexample found for this base.")
    return None

for num in range(4, 15):
    res = find_counterexample(num)
    if res:
        N, bp = res
        with open("/workspace/leanproject/Submission/success_sage_found.py", "w") as f:
            f.write(f"N = {N}\n")
            f.write(f"blocking_primes = {bp}\n")
        break
