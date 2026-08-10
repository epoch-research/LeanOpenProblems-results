import math
import sys
from sympy import isprime
from sympy.ntheory.modular import crt

X = 10**40  # $N$ will be around 10^20, which is well below 1.27 * 10^24

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

primes_3mod4 = [p for p in range(3, 10000) if isprime(p) and p % 4 == 3]

# Start with initial blocked list
blocked = [26, 104, 314, 416, 1256, 1664, 5024, 6656, 20096, 26624, 73274, 80384]

iteration = 1
while True:
    print(f"\nIteration {iteration}, blocked count: {len(blocked)}", flush=True)
    
    used_primes = []
    primes_set = {3, 7}
    for v in blocked:
        is_sq = (math.isqrt(v)**2 == v)
        found_p = False
        for p in primes_3mod4:
            if p not in primes_set:
                if is_sq or pow(v % p, (p - 1) // 2, p) == 1:
                    primes_set.add(p)
                    used_primes.append((v, p))
                    found_p = True
                    break
        if not found_p:
            print(f"ERROR: Could not find prime to block v = {v}", flush=True)
            sys.exit(1)
            
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
        
    print(f"Candidate n digits: {len(str(n))}", flush=True)
    
    n2 = n*n
    V_all = get_V_all(n2)
    print(f"V_all size: {len(V_all)}", flush=True)
    
    failing_vs = []
    primes_check = [3, 7] + [p for _, p in used_primes]
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
        print("\nSUCCESS! GUARANTEED COUNTEREXAMPLE FOUND!", flush=True)
        print(f"n0 = {n}", flush=True)
        print(f"used_primes = {used_primes}", flush=True)
        print(f"blocked = {blocked}", flush=True)
        break
    else:
        print(f"Failed: {len(failing_vs)} failing v's. First few: {failing_vs[:5]}", flush=True)
        added = 0
        for fv in failing_vs:
            if fv not in blocked:
                blocked.append(fv)
                added += 1
        blocked.sort()
        print(f"Added {added} new v's to blocked.", flush=True)
        iteration += 1
