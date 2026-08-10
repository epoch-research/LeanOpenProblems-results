import math
import sympy
import sys

divs_1680 = {1, 23, 73, 1679}
primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199]

max_exps = [30, 20, 12, 10, 8, 7, 6, 6, 5, 5, 4, 4, 3, 3, 3, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]

limit = 10**15

found = False

def test_exps(exps):
    global found
    g = 1
    s = 1
    for p, e in zip(primes, exps):
        if e > 0:
            g *= p**e
            s *= (p**(e+1) - 1) // (p - 1)
    
    s_prime = s - g
    gc = math.gcd(s, g)
    val = s_prime // gc
    if val in divs_1680:
        b = g // gc
        k = 1679 // val
        p = k * b - 1
        if p > 1 and g % p != 0 and sympy.isprime(p):
            a = s // gc
            if math.gcd(k * a, p) == 1:
                print(f"FOUND for 1680: g = {g}, p = {p}, i = {g * p}", flush=True)
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

print("Starting memory-efficient backtracking search for 1680...", flush=True)
search(0, [], 1)
print("Finished. Found nothing.", flush=True)
