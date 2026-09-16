import math

def a(n):
    num = math.factorial(6*n) * (3**n)
    den = math.factorial(3*n) * math.factorial(2*n)
    for k in range(1, n+1):
        den *= (2*n + 3*k)
    return num // den

for p in [5, 7, 11, 13, 17, 19, 23, 29, 31]:
    for r in [1, 2]:
        for n in [1, 2, 3]:
            v1 = a(n * p**r)
            v2 = a(n * p**(r-1))
            if v1 % (p**(3*r)) != v2 % (p**(3*r)):
                print(f"Counterexample: p={p}, r={r}, n={n}")
                exit(1)
print("All passed.")
