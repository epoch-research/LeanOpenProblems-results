from sympy import primerange, isprime, factorint

primes_q = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

def is_qr(p, q):
    val = (1 - 4*p) % q
    for x in range(q):
        if (x*x) % q == val:
            return True
    return False

exceptions = []
for p in primerange(199, 100000000):
    covered = False
    for q in primes_q:
        if is_qr(p, q):
            covered = True
            break
    if not covered:
        exceptions.append(p)

print(f"Total exceptions: {len(exceptions)}")

exception_data = []
for p in exceptions:
    found = False
    for k in range(2, 47):
        val = k**2 - k + p
        if not isprime(val):
            factors = factorint(val)
            d = min(factors.keys())
            exception_data.append((p, k, d))
            found = True
            break
    assert found, f"No witness for p={p}"

print("First few exception data:", exception_data[:10])
