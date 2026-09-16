import math

def a(n):
    num = math.factorial(6*n) * (3**n)
    den = math.factorial(3*n) * math.factorial(2*n)
    for k in range(1, n+1):
        den *= (2*n + 3*k)
    return num // den

primes = [5, 7, 11, 13]
for p in primes:
    for r in [2, 3]:
        for n in range(1, 10):
            v1 = a(n * p**r)
            v2 = a(n * p**(r-1))
            mod = p**(3*r)
            if v1 % mod != v2 % mod:
                print(f"Counterexample! p={p}, r={r}, n={n}")
                exit(0)
print("Checked up to r=3, n=9")
