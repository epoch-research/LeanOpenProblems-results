import math
import sys
sys.set_int_max_str_digits(1000000)

def a(n):
    num = math.factorial(6*n) * (3**n)
    den = math.factorial(3*n) * math.factorial(2*n)
    for k in range(1, n+1):
        den *= (2*n + 3*k)
    return num // den

primes = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
for p in primes:
    v1 = a(p)
    v2 = a(1)
    if v1 % (p**3) != v2 % (p**3):
        print(f"Counterexample: p={p}, r=1, n=1")
        exit(1)
print("All passed up to 97.")
