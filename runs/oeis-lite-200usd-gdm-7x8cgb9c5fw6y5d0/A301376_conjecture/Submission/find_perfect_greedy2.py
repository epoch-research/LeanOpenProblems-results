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
    
    # Greedy set cover to find a set of primes covering 'blocked'
    uncovered = set(blocked)
    chosen_primes = [] # list of (p, r)
    
    while uncovered:
        best_p = None
        best_r = None
        best_covered = set()
        
        # We only check the first 2000 primes (keep it extremely fast and small primes)
        for p in primes_3mod4[:2000]:
            if any(p == cp[0] for cp in chosen_primes):
                continue
            
            # Count frequencies of v % p for v in uncovered
            freq = {}
            for v in uncovered:
                r = v % p
                freq[r] = freq.get(r, 0) + 1
                
            for r, count in freq.items():
                if count > len(best_covered):
                    # Check if r is quadratic residue mod p
                    if r == 0 or pow(r, (p-1)//2, p) == 1:
                        covered = set(v for v in uncovered if v % p == r)
                        best_covered = covered
                        best_p = p
                        best_r = r
                        
        if len(best_covered) == 0:
            print("ERROR: Could not find any prime to block remaining v's!")
            print("Remaining:", uncovered)
            sys.exit(1)
            
        chosen_primes.append((best_p, best_r))
        uncovered -= best_covered
        
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
