import math
from sympy import isprime
from sympy.ntheory.modular import crt

# Generate V_all up to a limit
def get_V_all(limit):
    V = [1]
    for s in range(40):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        if fs >= limit:
            break
        for i in range(160):
            val = fs * 4**i
            if val >= limit:
                break
            if val not in V:
                V.append(val)
    V.sort()
    return V

# Greedy CRT covering algorithm
def find_small_counterexample():
    # Use primes congruent to 3 mod 4
    primes = [p for p in range(3, 1000) if isprime(p) and p % 4 == 3]
    
    # We want a set of primes to use
    # Let's try different number of primes, starting from 10
    for K in range(6, 25):
        used_primes = primes[:K]
        prod = 1
        for p in used_primes:
            prod *= p**2
        
        limit = prod**2
        V_all = get_V_all(limit)
        print(f"K={K}, prod digits={len(str(prod))}, V_all size={len(V_all)}")
        
        # We want to find residues r_p mod p^2 for each p in used_primes
        # such that for all v in V_all with v < n^2, n^2 - v is blocked.
        # Since n < prod, we can choose a residue n mod prod.
        # Specifically, we can run a greedy search.
        # Let's define the set of blocked v.
        # We can build n iteratively.
        # Start with a list of blocked v that we must cover.
        # Actually, let's use the iterative approach from find_perfect_iterative.py
        blocked = [26, 104, 314, 416, 1256, 1664, 5024, 6656]
        # Filter blocked to only those < limit
        blocked = [b for b in blocked if b < limit]
        
        iteration = 1
        while iteration <= 30:
            # For each v in blocked, choose a prime p from used_primes
            # such that v is a QR mod p.
            # To be smart, we try to choose primes that cover v.
            used_primes_for_blocked = []
            primes_set = {3, 7} # 3 and 7 are reserved for 9 and 49
            
            success = True
            for v in blocked:
                is_sq = (int(v**0.5)**2 == v)
                found_p = False
                for p in used_primes:
                    if p not in primes_set:
                        if is_sq or pow(v % p, (p - 1) // 2, p) == 1:
                            primes_set.add(p)
                            used_primes_for_blocked.append((v, p))
                            found_p = True
                            break
                if not found_p:
                    success = False
                    break
            
            if not success:
                # Not enough primes in used_primes to cover the blocked set
                break
                
            moduli = [9, 49]
            residues = [1, 15]
            for v, p in used_primes_for_blocked:
                moduli.append(p**2)
                # find a root mod p
                root = -1
                for x in range(p):
                    if (x*x) % p == v % p:
                        root = x
                        break
                # find a lift mod p^2
                lift = -1
                for k in range(p):
                    x = root + k*p
                    if (x*x - v) % (p**2) != 0:
                        lift = x
                        break
                residues.append(lift)
                
            n, prod_curr = crt(moduli, residues)
            n = int(n)
            prod_curr = int(prod_curr)
            if n % 2 == 0:
                n += prod_curr
                
            # Verify if n is a counterexample
            n2 = n*n
            is_counter = True
            failing_v = None
            
            # Get V_all for n^2
            V_curr = [v for v in V_all if v < n2]
            
            for v in V_curr:
                val = n2 - v
                found_block = False
                for p in [3, 7] + [p for _, p in used_primes_for_blocked]:
                    if val % p == 0 and val % (p*p) != 0:
                        found_block = True
                        break
                if not found_block:
                    # Let's check other primes in used_primes
                    for p in used_primes:
                        if val % p == 0:
                            count = 0
                            temp = val
                            while temp % p == 0:
                                count += 1
                                temp //= p
                            if count % 2 != 0:
                                found_block = True
                                break
                if not found_block:
                    failing_v = v
                    is_counter = False
                    break
                    
            if is_counter:
                print(f"FOUND SMALL COUNTEREXAMPLE!")
                print(f"n = {n}")
                print(f"n^2 = {n2}")
                print(f"Number of digits of n: {len(str(n))}")
                print(f"used_primes_for_blocked: {used_primes_for_blocked}")
                return n, used_primes_for_blocked
            else:
                if failing_v not in blocked:
                    blocked.append(failing_v)
                    blocked.sort()
                iteration += 1

find_small_counterexample()
