import sys
from sympy import isprime, factorint

N = 1048576
N2 = N * N

def get_V_all(N2):
    V = {1}
    for s in range(10):
        fs = (10 * 16**s + 16 * 4**s + 10) // 9
        for i in range(20):
            val = fs * 4**i
            if val < N2:
                V.add(val)
    return sorted(list(V))

V_all = get_V_all(N2)
print("V_all size:", len(V_all))

blocking_primes = {}
for v in V_all:
    diff = N2 - v
    factors = factorint(diff)
    found = False
    # Sort primes ascending to prefer smaller primes
    for p in sorted(factors.keys()):
        if p % 4 == 3 and factors[p] == 1:
            blocking_primes[v] = p
            found = True
            break
    if not found:
        print(f"Failed to find exact blocking prime for v = {v}! Factors: {factors}")
        sys.exit(1)

print("SUCCESS! Found exact blocking prime for all elements!")
print("blocking_primes =", blocking_primes)
