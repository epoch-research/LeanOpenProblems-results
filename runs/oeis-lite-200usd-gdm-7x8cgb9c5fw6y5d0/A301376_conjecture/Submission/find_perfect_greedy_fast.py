import math
import sys
from sympy import isprime
from sympy.ntheory.modular import crt

sys.set_int_max_str_digits(200000)

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

print("Precomputing primes congruent to 3 mod 4...")
primes_3mod4 = [p for p in range(11, 100000) if isprime(p) and p % 4 == 3]
print(f"Precomputed {len(primes_3mod4)} primes.")

# Start with a list of failing v's that we know we must cover
blocked = [26, 104, 314, 416, 1256, 1664, 5024, 6656, 20096, 26624, 73274, 80384]

iteration = 1
while True:
    print(f"\n--- Iteration {iteration} ---")
    print(f"Number of target v's to block: {len(blocked)}")
    sys.stdout.flush()
    
    # We only check the first 2000 primes for speed
    candidate_primes = primes_3mod4[:2000]
    
    # Precompute residues and whether they are quadratic residues
    # matrix[p_idx][v_idx] = (v % p, is_qr)
    print("Precomputing residues...")
    sys.stdout.flush()
    
    # To speed up QR checks, we precompute QR sets for each prime
    qr_sets = []
    for p in candidate_primes:
        qrs = {0}
        for x in range(1, p):
            qrs.add((x*x) % p)
        qr_sets.append(qrs)
        
    # Precompute modulo values for each v and prime
    # residues_matrix[p_idx] is a list of (r, is_qr) for each v in blocked
    residues_matrix = []
    for p_idx, p in enumerate(candidate_primes):
        qrs = qr_sets[p_idx]
        row = []
        for v in blocked:
            r = v % p
            is_qr = r in qrs
            row.append((r, is_qr))
        residues_matrix.append(row)
        
    print("Precomputation finished. Starting greedy selection...")
    sys.stdout.flush()
    
    # Greedy set cover to find a set of primes covering 'blocked'
    # We represent the uncovered set as indices into 'blocked'
    uncovered_indices = set(range(len(blocked)))
    chosen_primes = [] # list of (p, r)
    
    while uncovered_indices:
        best_p_idx = None
        best_r = None
        best_covered_indices = set()
        best_count = 0
        
        for p_idx, p in enumerate(candidate_primes):
            if any(p == cp[0] for cp in chosen_primes):
                continue
                
            row = residues_matrix[p_idx]
            
            # Count frequencies of residues for uncovered indices
            freq = {}
            for v_idx in uncovered_indices:
                r, is_qr = row[v_idx]
                if is_qr:
                    freq[r] = freq.get(r, 0) + 1
                    
            for r, count in freq.items():
                if count > best_count:
                    best_count = count
                    best_p_idx = p_idx
                    best_r = r
                    
        if best_count == 0:
            print("ERROR: Could not find any prime to block remaining v's!")
            print("Remaining indices:", uncovered_indices)
            print("Remaining values:", [blocked[idx] for idx in uncovered_indices])
            sys.exit(1)
            
        # Find the covered indices for the best prime
        best_p = candidate_primes[best_p_idx]
        best_row = residues_matrix[best_p_idx]
        best_covered_indices = set(v_idx for v_idx in uncovered_indices if best_row[v_idx][0] == best_r)
        
        chosen_primes.append((best_p, best_r))
        uncovered_indices -= best_covered_indices
        
    print(f"Chosen primes for cover ({len(chosen_primes)}): {chosen_primes}")
    
    # Solve CRT to find candidate n
    moduli = [9, 49]
    residues = [1, 15] # n^2 = 1 mod 9, n^2 = 8 mod 49
    for p, r in chosen_primes:
        moduli.append(p**2)
        # find root mod p
        root = -1
        for x in range(p):
            if (x*x) % p == r % p:
                root = x
                break
        # lift mod p^2
        best_k = -1
        best_fail_count = 999999
        for k in range(p):
            x = root + k*p
            fail_count = 0
            # check how many v's in blocked fail
            # we only care about those v's in blocked that are covered by p
            covered_vs = [v for v in blocked if v % p == r]
            for fv in covered_vs:
                if (x*x - fv) % (p**2) == 0:
                    fail_count += 1
            if fail_count < best_fail_count:
                best_fail_count = fail_count
                best_k = k
                
        lift = root + best_k * p
        residues.append(lift)
        if best_fail_count > 0:
            print(f"Warning: prime {p} has {best_fail_count} unavoidable fails with lift {lift}")
            
    n, prod = crt(moduli, residues)
    n = int(n)
    prod = int(prod)
    if n % 2 == 0:
        n += prod
        
    print(f"Candidate n digits: {len(str(n))}")
    
    # Generate V_all up to n^2
    n2 = n*n
    V_all = get_V_all(n2)
    print(f"V_all size: {len(V_all)}")
    sys.stdout.flush()
    
    # Find all failing v's
    failing_vs = []
    primes_check = [3, 7] + [p for p, _ in chosen_primes]
    for v in V_all:
        val = n2 - v
        found_block = False
        for p in primes_check:
            if val % p == 0 and val % (p*p) != 0:
                found_block = True
                break
        if not found_block:
            failing_vs.append(v)
            
    if not failing_vs:
        print("\nSUCCESS! 100% GUARANTEED COUNTEREXAMPLE FOUND!")
        print(f"n0 = {n}")
        print(f"used_primes = {chosen_primes}")
        print(f"blocked = {blocked}")
        break
    else:
        print(f"Failed: {len(failing_vs)} failing v's. First few: {failing_vs[:5]}")
        sys.stdout.flush()
        added = 0
        for fv in failing_vs:
            if fv not in blocked:
                blocked.append(fv)
                added += 1
        blocked.sort()
        print(f"Added {added} new v's to blocked.")
        iteration += 1
