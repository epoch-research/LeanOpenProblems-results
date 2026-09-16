import math
import sys

def a(n):
    num = math.factorial(6*n) * (3**n)
    den = math.factorial(3*n) * math.factorial(2*n)
    for k in range(1, n+1):
        den *= (2*n + 3*k)
    return num // den

for p in [5, 7, 11]:
    for r in [1, 2, 3]:
        for n in range(1, 10):
            a_npr = a(n * p**r)
            a_npr1 = a(n * p**(r-1))
            mod = p**(3*r)
            if a_npr % mod != a_npr1 % mod:
                print(f"Counterexample! p={p}, n={n}, r={r}")
                sys.exit(0)
print("No counterexamples found.")
