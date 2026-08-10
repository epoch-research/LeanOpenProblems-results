import sympy

def is_provable(n):
    # We want to find a prime q such that:
    # 1. q^2 - 2q - 2 <= n
    # 2. n <= q^2 + 2q - 2
    # 3. 2q^2 - 1 <= 3n
    # Let's search primes q in a reasonable range around sqrt(n)
    limit = int((1.5 * n)**0.5) + 5
    for q in sympy.primerange(2, limit):
        cond1 = (q**2 - 2*q - 2 <= n)
        cond2 = (n <= q**2 + 2*q - 2)
        cond3 = (2*q**2 - 1 <= 3*n)
        if cond1 and cond2 and cond3:
            return q
    return None

unprovable = []
for n in range(3, 10000):
    q = is_provable(n)
    if q is None:
        unprovable.append(n)

print(f"Number of unprovable n < 10000: {len(unprovable)}")
print(f"Unprovable n: {unprovable}")
