def get_order(g, p):
    if p == 2:
        return 1
    # Find order of g mod p
    res = 1
    val = g % p
    while val != 1:
        val = (val * g) % p
        res += 1
    return res

import sympy

M_targets = [720, 1440, 2880]
for M in M_targets:
    primes_found = []
    for p in sympy.primerange(3, 10000):
        o = get_order(2, p)
        if M % o == 0:
            primes_found.append((p, o))
    print(f"M = {M}: Found {len(primes_found)} primes.")
    print([p for p, o in primes_found])
