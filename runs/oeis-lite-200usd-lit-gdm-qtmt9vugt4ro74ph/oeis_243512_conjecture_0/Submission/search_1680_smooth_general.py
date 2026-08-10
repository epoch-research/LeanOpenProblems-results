import math
import sympy
import sys

primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
max_exps = [30, 20, 12, 10, 8, 7, 6, 6, 5, 5, 4, 4, 3, 3, 3]

limit = 10**11
found = False
count = 0

def test_exps(exps):
    global found, count
    count += 1
    if count % 100000 == 0:
        print(f"Processed {count} smooth numbers...", flush=True)
    g = 1
    s = 1
    for p, e in zip(primes, exps):
        if e > 0:
            g *= p**e
            s *= (p**(e+1) - 1) // (p - 1)
    
    s_prime = s - g
    if s_prime <= 0:
        return
    gc = math.gcd(s_prime, g)
    val = s_prime // gc
    if val > 1679:
        return
        
    b_init = g // gc
    # Find all divisors of b_init that are < 1680
    divs = []
    for d in range(1, 1680):
        if b_init % d == 0:
            divs.append(d)
            
    for b in divs:
        if (1680 - b) % val == 0:
            m = (1680 - b) // val
            k = b_init // b
            p = m * k - 1
            if p > 1 and g % p != 0 and sympy.isprime(p):
                sig_gp = s * (p + 1)
                i_val = g * p
                gc_gp = math.gcd(sig_gp, i_val)
                if (sig_gp - i_val) // gc_gp == 1680:
                    print(f"FOUND PREIMAGE for 1680: g = {g}, p = {p}, i = {g * p}, b = {b}, val = {val}", flush=True)
                    found = True
                    sys.exit(0)

def search(idx, current_exps, current_g):
    if current_g > limit:
        return
    if idx > 0 and current_exps[-1] > 0:
        test_exps(current_exps)
    
    if idx == len(primes):
        return
        
    p = primes[idx]
    for e in range(max_exps[idx] + 1):
        nxt_g = current_g * (p**e)
        if nxt_g > limit:
            break
        current_exps.append(e)
        search(idx + 1, current_exps, nxt_g)
        current_exps.pop()

print("Starting general smooth backtracking search...", flush=True)
search(0, [], 1)
print("Finished. Found nothing.", flush=True)
