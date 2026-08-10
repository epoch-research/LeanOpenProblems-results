import math
from sympy import isprime, factorint
from sympy.ntheory.modular import crt

def solve():
    # Generate V
    V = [1]
    for s in range(5):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(25):
            val = fs * 4**i
            if val not in V:
                V.append(val)
    V.sort()

    # Precompute primes q = 3 mod 4 up to 1,000,000
    print("Generating primes...")
    primes_3mod4 = [p for p in range(3, 1000000) if isprime(p) and p % 4 == 3]
    print(f"Generated {len(primes_3mod4)} primes.")

    # We will search for a subset of target V to block with specific primes
    # To keep the candidate n as small as possible, let's try to block V[:M] for different M.
    # If we block V[:M], can we find a candidate n such that n^2 - v has a small prime factor
    # congruent to 3 mod 4 with odd exponent for all v < n^2?
    for M in range(5, 35):
        print(f"\n--- Trying M = {M} ---")
        # Find distinct primes for first M elements
        used_primes = []
        primes_set = set()
        for j in range(M):
            v = V[j]
            is_sq = (int(math.isqrt(v))**2 == v)
            found = False
            for p in primes_3mod4:
                if p not in primes_set:
                    if is_sq or pow(v % p, (p - 1) // 2, p) == 1:
                        primes_set.add(p)
                        used_primes.append((v, p))
                        found = True
                        break
            if not found:
                print(f"Could not find prime for v = {v}")
                break
        else:
            # Solve CRT
            moduli = [p**2 for v, p in used_primes]
            residues = []
            for v, p in used_primes:
                # find root
                root = -1
                for x in range(p):
                    if (x*x) % p == v % p:
                        root = x
                        break
                # lift mod p^2
                lift = -1
                for k in range(p):
                    x = root + k*p
                    if (x*x - v) % (p**2) != 0:
                        lift = x
                        break
                residues.append(lift)
                
            n, prod = crt(moduli, residues)
            n = int(n)
            prod = int(prod)
            if n % 2 == 0:
                n += prod
                
            print(f"Candidate n = {n}")
            print(f"Digits: {len(str(n))}")
            
            # Check if n is a counterexample!
            # For each v < n^2, we need to find a prime q in primes_3mod4 such that q divides n^2 - v to an odd power.
            is_counter = True
            failing_v = None
            
            for v in V:
                if v >= n*n: break
                
                # Check if we can find a blocking prime for n^2 - v
                val = n*n - v
                found_block = False
                for q in primes_3mod4:
                    if q * q > val:
                        # Since we only sieved up to 1M, if q*q > val and val > 1,
                        # val is either prime or has factors >= 1M.
                        # If val is prime and val % 4 == 3, then q = val is the blocking prime!
                        if isprime(val) and val % 4 == 3:
                            found_block = True
                        break
                    if val % q == 0:
                        count = 0
                        while val % q == 0:
                            count += 1
                            val //= q
                        if count % 2 != 0:
                            found_block = True
                            break
                            
                if not found_block:
                    # Double check with exact sum of two squares test
                    # Since we might have missed a prime > 1M, let's check with sympy's factorint
                    factors = factorint(n*n - v)
                    has_odd_3mod4 = False
                    for p, e in factors.items():
                        if p % 4 == 3 and e % 2 != 0:
                            has_odd_3mod4 = True
                            # Print the missed prime factor so we can see
                            print(f"Missed prime factor {p} for v = {v}")
                            break
                    if not has_odd_3mod4:
                        is_counter = False
                        failing_v = v
                        break
                        
            if is_counter:
                print(f"SUCCESS! COUNTEREXAMPLE FOUND: n = {n}")
                return
            else:
                print(f"Failed because of v = {failing_v}")

solve()
