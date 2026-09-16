import math

def a(n):
    num = math.factorial(6*n) * (3**n)
    den = math.factorial(3*n) * math.factorial(2*n)
    for k in range(1, n+1):
        den *= (2*n + 3*k)
    return num // den

p = 5
r = 1
for n in range(1, 100):
    v1 = a(n * p**r)
    v2 = a(n * p**(r-1))
    if v1 % (p**(3*r)) != v2 % (p**(3*r)):
        print(f"Counterexample: p={p}, r={r}, n={n}")
        exit(0)

print("No counterexample found for p=5, r=1, n up to 100")
