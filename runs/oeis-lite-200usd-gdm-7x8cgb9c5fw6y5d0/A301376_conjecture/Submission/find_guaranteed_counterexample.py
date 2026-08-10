import math
import sys
from sympy import isprime
from sympy.ntheory.modular import crt

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

# Precompute primes congruent to 3 mod 4 up to 200,000
print("Precomputing primes...")
sys.stdout.flush()
primes_3mod4 = [p for p in range(3, 200000) if isprime(p) and p % 4 == 3]
print(f"Found {len(primes_3mod4)} primes congruent to 3 mod 4.")
sys.stdout.flush()

# Start with a list of blocked v that we know need to be covered
blocked = [26, 104, 314, 416, 1256, 1664, 5024, 6656, 20096, 26624, 73274, 80384]

iteration = 1
while True:
    print(f"\nIteration {iteration}, blocked count: {len(blocked)}")
    sys.stdout.flush()
    
    # Choose a prime p for each v in blocked
    used_primes = []
    primes_set = {3, 7}
    for v in blocked:
        is_sq = (int(v**0.5)**2 == v)
        for p in primes_3mod4:
            if p not in primes_set:
                if is_sq or pow(v % p, (p - 1) // 2, p) == 1:
                    primes_set.add(p)
                    used_primes.append((v, p))
                    break
                    
    # Construct candidate n using CRT
    moduli = [9, 49]
    residues = [1, 15]
    for v, p in used_primes:
        moduli.append(p**2)
        # find root mod p
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
        
    print(f"Candidate n: {n}")
    print(f"Digits of n: {len(str(n))}")
    sys.stdout.flush()
    
    # Generate V_all up to n^2
    n2 = n*n
    V_all = get_V_all(n2)
    print(f"V_all size up to n^2: {len(V_all)}")
    sys.stdout.flush()
    
    is_counter = True
    failing_v = None
    
    # Check if any v in V_all is not blocked
    primes_check = [3, 7] + [p for _, p in used_primes]
    for idx, v in enumerate(V_all):
        val = n2 - v
        found_block = False
        for p in primes_check:
            if val % p == 0 and val % (p*p) != 0:
                found_block = True
                break
        if not found_block:
            failing_v = v
            is_counter = False
            break
            
    if is_counter:
        print("\nSUCCESS! GUARANTEED COUNTEREXAMPLE FOUND!")
        print(f"n0 = {n}")
        print(f"used_primes = {used_primes}")
        print(f"blocked = {blocked}")
        break
    else:
        print(f"Failed because of v = {failing_v}")
        sys.stdout.flush()
        if failing_v not in blocked:
            blocked.append(failing_v)
            blocked.sort()
        iteration += 1
