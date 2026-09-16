import math

def a(n):
    num = math.factorial(6*n) * (3**n)
    den = math.factorial(3*n) * math.factorial(2*n)
    for k in range(1, n+1):
        den *= (2*n + 3*k)
    return num // den

primes = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
for p in primes:
    for r in [1, 2]:
        for n in range(1, 10):
            v1 = a(n * p**r)
            v2 = a(n * p**(r-1))
            mod = p**(3*r)
            if v1 % mod != v2 % mod:
                print(f"Counterexample! p={p}, r={r}, n={n}")
                exit(0)
print("Checked many.")
