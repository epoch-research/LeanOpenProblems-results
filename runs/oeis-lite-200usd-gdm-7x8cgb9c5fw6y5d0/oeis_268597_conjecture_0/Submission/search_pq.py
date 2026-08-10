import sympy

def phi(n):
    return sympy.totient(n)

# Let's search for a general formula for x given m = p * q with p, q >= 5 primes.
# We want (x - 1) % phi(x) == pq - 1, i.e., x - pq is a multiple of phi(x).
# Let's test for various pairs (p, q).

pairs = [(5, 7), (5, 11), (5, 13), (7, 11), (7, 13), (11, 13)]

for p, q in pairs:
    m = p * q
    n = m - 1
    print(f"\nm = {m} ({p} * {q}):")
    found = []
    for x in range(1, 100000):
        if (x - 1) % phi(x) == n:
            factors = sympy.factorint(x)
            # Express factors in terms of p, q and other small primes
            factor_str = " * ".join([f"{pr}^{ext}" for pr, ext in factors.items()])
            found.append((int(x), str(factor_str), int(phi(x)), int((x-1)//phi(x))))
    for f in found[:15]:
        print(f"  x = {f[0]:5d} = {f[1]:20s}, phi(x) = {f[2]:5d}, k = {f[3]}")
