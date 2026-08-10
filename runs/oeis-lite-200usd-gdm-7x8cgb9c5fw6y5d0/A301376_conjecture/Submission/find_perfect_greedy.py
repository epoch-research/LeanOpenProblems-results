import math
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
        
        for p in primes_3mod4:
            if any(p == cp[0] for cp in chosen_primes):
                continue
            # find the best residue mod p
            # since we want to block v, we want (n^2 - v) % p == 0 => n^2 = v mod p.
            # So the residue r we choose for n^2 mod p must be a quadratic residue mod p.
            # If we choose r, then for any v with v % p == r, v % p is blocked.
            # So we check all quadratic residues mod p (including 0)
            qrs = {0}
            for x in range(1, p):
                qrs.add((x*x) % p)
                
            for r in qrs:
                covered = set(v for v in uncovered if v % p == r)
                if len(covered) > len(best_covered):
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
    residues = [1, 15] # n^2 = 1 mod 9 (blocks powers of 4), n^2 = 8 mod 49
    for p, r in chosen_primes:
        moduli.append(p**2)
        # find root mod p
        root = -1
        for x in range(p):
            if (x*x) % p == r % p:
                root = x
                break
        # lift mod p^2
        # we want (n^2 - v) % p^2 != 0 for all v in the covered set.
        # Wait! If multiple v's are covered, can we find a single lift that works for ALL of them?
        # Let's check!
        # The lift is n mod p^2.
        # For each v covered by (p, r), we want (n^2 - v) % p^2 != 0.
        # Since n = root + k * p, n^2 - v = root^2 - v + 2*root*k*p mod p^2.
        # Since v % p = root^2 % p = r % p, root^2 - v is a multiple of p.
        # So root^2 - v + 2*root*k*p = p * ((root^2 - v)/p + 2*root*k).
        # Since p is odd, and root != 0 mod p, 2*root is invertible mod p.
        # So there is EXACTLY ONE value of k mod p that makes this 0 mod p^2!
        # Thus, for each v, there is exactly one k_v ∈ {0, ..., p-1} that we must AVOID!
        # Since we have p possible values of k, and we want to avoid k_v for all v in the covered set,
        # we can do this as long as the number of v's in the covered set is less than p,
        # or if we can find some k that is not in the avoid set!
        # If the covered set is large, we might have to be careful.
        # Let's find a lift k ∈ {0, ..., p-1} that minimizes the number of v's with (n^2 - v) % p^2 == 0.
        # Ideally, 0!
        best_k = -1
        best_fail_count = 999999
        for k in range(p):
            x = root + k*p
            fail_count = 0
            # check how many v's in blocked (or in V_all) fail
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
        
    print(f"Candidate n: {n}")
    print(f"Digits of n: {len(str(n))}")
    
    # Generate V_all up to n^2
    n2 = n*n
    V_all = get_V_all(n2)
    print(f"V_all size: {len(V_all)}")
    
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
