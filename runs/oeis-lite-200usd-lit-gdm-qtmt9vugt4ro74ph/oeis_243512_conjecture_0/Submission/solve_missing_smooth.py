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

# Let's generate and test on the fly to save memory
found = {}

def test_g(g):
    s = sympy.divisor_sigma(g)
    gc = math.gcd(s, g)
    val = (s - g) // gc
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

# We will generate smooth numbers in increasing order of size to find small i first.
# To do this, we can use a priority queue or just generate up to a certain limit.
# Since we want to search up to 10^12, let's use a standard search or recursive generator with a limit.
limit = 10**12

# Let's do a simple recursive generation with different prime sets
def gen(idx, val):
    if val > limit:
        return
    test_g(val)
    for i in range(idx, len(primes)):
        p = primes[i]
        if val * p > limit:
            break
        gen(i, val * p)

print("Starting smooth search...")
gen(0, 1)
print("Finished smooth search.")
print("Found solutions:", found)
