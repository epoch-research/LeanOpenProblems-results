import math
import sys
from sympy import isprime

V = [1]
for s in range(5):
    fs = (10 * 16**s + 16 * 4**s + 10) // 9
    for i in range(25):
        val = fs * 4**i
        if val not in V:
            V.append(val)
V.sort()

# Precompute primes congruent to 3 mod 4 up to 100,000
primes_3mod4 = [p for p in range(3, 100000) if isprime(p) and p % 4 == 3]

blocked = [26, 104, 314, 416, 1256, 1664, 5024, 6656, 20096, 26624, 73274, 80384]

iteration = 1
while iteration <= 50:
    print(f'Iteration {iteration}, blocked count: {len(blocked)}')
    sys.stdout.flush()
    
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
                    
    moduli = [9, 49]
    residues = [1, 15]
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
        
    from sympy.ntheory.modular import crt
    n, prod = crt(moduli, residues)
    n = int(n)
    prod = int(prod)
    if n % 2 == 0:
        n += prod
        
    print(f'Candidate n: {n}')
    print(f'Digits: {len(str(n))}')
    sys.stdout.flush()
    
    is_counter = True
    failing_v = None
    for idx, v in enumerate(V):
        if v >= n*n: break
        
        val = n*n - v
        found_block = False
        
        # 1. Check if blocked by our moduli
        for p in [3, 7] + [p for _, p in used_primes]:
            if val % p == 0 and val % (p*p) != 0:
                found_block = True
                break
                
        # 2. Check if blocked by any other small prime congruent to 3 mod 4 up to 50,000
        if not found_block:
            for q in primes_3mod4[:5000]: # check first 5000 primes
                if q*q > val: break
                if val % q == 0:
                    count = 0
                    while val % q == 0:
                        count += 1
                        val //= q
                    if count % 2 != 0:
                        found_block = True
                        break
                        
        # 3. Check if val is prime and congruent to 3 mod 4
        if not found_block:
            if isprime(val) and val % 4 == 3:
                found_block = True
                
        if not found_block:
            failing_v = v
            is_counter = False
            break
            
    if is_counter:
        print(f'SUCCESS! COUNTEREXAMPLE FOUND: {n}')
        print(f'used_primes = {used_primes}')
        print(f'blocked = {blocked}')
        break
    else:
        print(f'Failed because of v = {failing_v}')
        sys.stdout.flush()
        if failing_v not in blocked:
            blocked.append(failing_v)
            blocked.sort()
        iteration += 1
