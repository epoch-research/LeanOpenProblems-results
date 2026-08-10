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

    print("Generating primes...")
    primes_3mod4 = [p for p in range(3, 10000) if isprime(p) and p % 4 == 3]
    print(f"Generated {len(primes_3mod4)} primes.")

    # Moduli and residues for 3 and 7 strategy
    # n^2 = 1 mod 9, n^2 = 8 mod 49
    # This blocks all powers of 4!
    
    # Let's try to block V[:K] where K is the number of elements of V we want to cover.
    # Since powers of 4 are already blocked, we only need to cover the remaining elements in V[:K].
    for K in range(10, 40):
        target_V = V[:K]
        # Which elements are NOT covered by 9 and 49?
        uncovered = []
        for v in target_V:
            if (1 - v) % 9 in {3, 6}:
                continue
            if (8 - v) % 49 in {7, 14, 21, 28, 35, 42}:
                continue
            uncovered.append(v)
            
        print(f"\nK = {K}. Target V: {len(target_V)}. Uncovered by 3/7: {len(uncovered)}: {uncovered}")
        
        # Find distinct primes to block the uncovered elements
        used_primes = []
        primes_set = {3, 7}
        for v in uncovered:
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
            moduli = [9, 49]
            residues = [1, 15] # n = 1 mod 9, n = 15 mod 49 (which gives n^2 = 8 mod 49)
            
            for v, p in used_primes:
                moduli.append(p**2)
                root = -1
                for x in range(p):
                    if (x*x) % p == v % p:
                        root = x
                        break
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
            is_counter = True
            failing_v = None
            
            for v in V:
                if v >= n*n: break
                
                # Check if n^2 - v has an odd 3mod4 exponent
                val = n*n - v
                found_block = False
                
                # Check 3 and 7 first
                if (1 - v) % 9 in {3, 6}:
                    found_block = True
                elif (8 - v) % 49 in {7, 14, 21, 28, 35, 42}:
                    found_block = True
                else:
                    # Check the extra primes
                    for ev, ep in used_primes:
                        if (n*n - v) % ep == 0 and (n*n - v) % (ep**2) != 0:
                            found_block = True
                            break
                            
                if not found_block:
                    # Check other primes up to 1000000
                    for q in range(3, 100000):
                        if isprime(q) and q % 4 == 3:
                            if val % q == 0:
                                count = 0
                                while val % q == 0:
                                    count += 1
                                    val //= q
                                if count % 2 != 0:
                                    found_block = True
                                    break
                                    
                if not found_block:
                    # Double check with exact test
                    factors = factorint(n*n - v)
                    has_odd_3mod4 = False
                    for p, e in factors.items():
                        if p % 4 == 3 and e % 2 != 0:
                            has_odd_3mod4 = True
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
