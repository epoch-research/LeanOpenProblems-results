import math
import sys
from sympy import isprime
from sympy.ntheory.modular import crt

n_old = 662586139984204484076253051
n2_old = n_old * n_old

used_primes = [(11, 2), (19, 3), (23, 3), (31, 2), (43, 40), (47, 18), (59, 48), (67, 49)]

def get_V_all(limit):
    V = {1}
    for s in range(45):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        if fs >= limit:
            break
        for i in range(90):
            val = fs * 4**i
            if val >= limit:
                break
            V.add(val)
    return sorted(list(V))

V_all = get_V_all(n2_old)
print(f"V_all size for 27-digit N: {len(V_all)}")

primes_check = [3, 7] + [p for p, _ in used_primes]

unblocked = []
v_to_prime = {}

for v in V_all:
    val = n2_old - v
    found = False
    for p in primes_check:
        if val % p == 0 and val % (p*p) != 0:
            v_to_prime[v] = p
            found = True
            break
    if not found:
        unblocked.append(v)

if unblocked:
    print(f"FAILED! {len(unblocked)} elements are not blocked.")
    print("First few unblocked:", unblocked[:10])
else:
    print("SUCCESS! 100% GUARANTEED 27-DIGIT COUNTEREXAMPLE!")
    print("used_primes =", used_primes)
