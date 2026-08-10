import math
import sympy

missing_dict = {
    1680: {1, 23, 73, 1679},
    2226: {1, 5, 25, 89, 445, 2225},
    3432: {1, 47, 73, 3431},
    3570: {1, 43, 83, 3569},
    3744: {1, 19, 197, 3743},
    4488: {1, 7, 641, 4487}
}

primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

# We want to search for g of the form product(p^e) up to 10^25.
# To do this efficiently, we can use backtracking with a maximum value of 10^25.
# Since we only want s_prime/gc to be in the divisor sets, we can check each g.

found = {}

def get_sigma_and_s_prime(exps):
    # exps is a list of exponents for the primes
    g = 1
    s = 1
    for p, e in zip(primes, exps):
        if e > 0:
            g *= p**e
            s *= (p**(e+1) - 1) // (p - 1)
    return g, s

def test_exps(exps):
    g, s = get_sigma_and_s_prime(exps)
    if g > 10**25:
        return
    s_prime = s - g
    gc = math.gcd(s, g)
    val = s_prime // gc
    b = g // gc
    a = s // gc
    for n, divs in missing_dict.items():
        if n in found:
            continue
        if val in divs:
            k = (n - 1) // val
            p = k * b - 1
            if p > 1 and g % p != 0 and sympy.isprime(p) and math.gcd(k * a, p) == 1:
                found[n] = (g, p, g * p)
                print(f"FOUND for {n}: g = {g}, p = {p}, i = {g * p}")

# Backtracking generator for exponents
# We can limit the search space by choosing max exponents
max_exps = [25, 15, 10, 8, 6, 5, 4, 4, 3, 3, 3, 2, 2, 2, 2]

def search(idx, current_exps, current_g):
    if current_g > 10**25:
        return
    if idx > 0:
        test_exps(current_exps)
    
    if idx == len(primes):
        return
        
    p = primes[idx]
    # Try different exponents
    for e in range(max_exps[idx] + 1):
        nxt_g = current_g * (p**e)
        if nxt_g > 10**25:
            break
        current_exps.append(e)
        search(idx + 1, current_exps, nxt_g)
        current_exps.pop()

print("Starting large smooth search...")
search(0, [], 1)
print("Finished. Found:", found)
