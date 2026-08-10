import sys
from sympy import isprime, factorint

N = 16384
N2 = N * N

def get_V_all(N2_limit):
    V = {1}
    for s in range(10):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(20):
            val = fs * 4**i
            if val < N2_limit:
                V.add(val)
    return sorted(list(V))

V_all = [v for v in get_V_all(N2) if v < N2]
print(f"N = {N}, N^2 = {N2}, V_all size: {len(V_all)}")

blocking_primes = {}
all_covered = True

for v in V_all:
    diff = N2 - v
    if diff == 0:
        print(f"v = {v} is equal to N2!")
        all_covered = False
        continue
        
    # Factorize diff to find any prime congruent to 3 mod 4 with odd exponent
    factors = factorint(diff)
    found_p = None
    for p, exp in factors.items():
        if p % 4 == 3 and exp % 2 != 0:
            found_p = p
            break
    if found_p is not None:
        blocking_primes[v] = found_p
    else:
        print(f"v = {v} (diff = {diff}) has no prime factor congruent to 3 mod 4 with odd exponent!")
        all_covered = False

if all_covered:
    print("SUCCESS! All elements blocked!")
    print(f"Blocking primes used: {blocking_primes}")
    print(f"Max blocking prime: {max(blocking_primes.values())}")
else:
    print("Failed to find blocking primes for all elements.")
