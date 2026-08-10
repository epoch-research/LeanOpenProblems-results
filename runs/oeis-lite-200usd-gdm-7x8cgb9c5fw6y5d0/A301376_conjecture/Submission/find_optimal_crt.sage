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

def run_search(N_max):
    limit = N_max * N_max
    V_target = [v for v in all_V if v < limit]
    print(f"N_max = {N_max}, V_target size = {len(V_target)}")
    
    # Greedily pick primes p = 3 mod 4 and residues
    # We want to cover as many of V_target as possible
    primes_pool = [p for p in prime_range(3, 100) if p % 4 == 3]
    
    selected_primes = []
    selected_residues = {}
    uncovered = list(V_target)
    
    while len(uncovered) > 0 and len(selected_primes) < 8:
        best_p = None
        best_r = None
        best_cov = -1
        
        for p in primes_pool:
            if p in selected_primes:
                continue
            # For each possible residue r mod p, count how many uncovered v have v % p == r^2 % p
            cov_for_r = [0] * p
            for v in uncovered:
                v_mod = v % p
                if v_mod == 0:
                    cov_for_r[0] += 1
                elif pow(v_mod, (p-1)//2, p) == 1:
                    # v_mod is a quadratic residue mod p. Find its square root
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
        # Remove covered elements
        new_uncovered = []
        r2 = (best_r * best_r) % best_p
        for v in uncovered:
            if v % best_p != r2:
                new_uncovered.append(v)
        uncovered = new_uncovered
        print(f"Picked prime {best_p}, residue {best_r} (covers {best_cov} elements). Uncovered remaining: {len(uncovered)}")
        
    # Solve CRT with selected primes, and also modulo 2 to force N to be odd
    moduli = [2] + selected_primes
    residues = [1] + [selected_residues[p] for p in selected_primes]
    from math import prod as math_prod
    base_prod = math_prod(moduli)
    N0 = int(crt(residues, moduli))
    
    print(f"CRT base: N0 = {N0}, prod = {base_prod}, digits = {len(str(base_prod))}")
    
    # Now check candidates N = N0 + k * prod
    # Since we want N <= N_max, let's see if there is any candidate
    print("Searching for counterexample...")
    for k in range(1000):
        N = N0 + k * base_prod
        if N >= N_max:
            print(f"Exceeded N_max at k = {k}")
            break
        N2 = N * N
        V_actual = [v for v in all_V if v < N2]
        
        # Verify if N is a counterexample
        all_blocked = True
        blocking_primes = {}
        for v in V_actual:
            diff = N2 - v
            # Find a blocking prime p = 3 mod 4
            found_p = None
            # Check selected primes first
            for p in selected_primes:
                if diff % p == 0 and diff % (p*p) != 0:
                    found_p = p
                    break
            if found_p is None:
                # Factor to find one
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
            print(f"SUCCESS! Found N = {N} (k = {k})")
            print(f"N^2 = {N2}")
            print(f"V_all size = {len(V_actual)}")
            print(f"Number of distinct blocking primes: {len(set(blocking_primes.values()))}")
            print(f"blocking_primes = {blocking_primes}")
            return N, blocking_primes
            
    return None

# Try N_max = 5 * 10^6
res = run_search(10**7)
if res:
    N, bp = res
    with open("/workspace/leanproject/Submission/success_sage_found.py", "w") as f:
        f.write(f"N = {N}\n")
        f.write(f"blocking_primes = {bp}\n")
else:
    print("Failed to find any counterexample.")
