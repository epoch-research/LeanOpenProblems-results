import sympy
from sympy import binomial, Symbol

# We can define a(n) using factorial ratios
memo = {}

def get_a(n):
    if n in memo:
        return memo[n]
    if n == 0:
        res = 1
    elif n % 2 == 0:
        k = n // 2
        res = int(sympy.factorial(18*k) * sympy.factorial(4*k) * sympy.factorial(3*k) / (sympy.factorial(9*k) * sympy.factorial(8*k) * sympy.factorial(6*k) * sympy.factorial(2*k)))
    else:
        k = (n - 1) // 2
        res = int(sympy.factorial(4*k+2) * sympy.factorial(9*k+4) / (sympy.factorial(8*k+4) * sympy.factorial(2*k+1) * sympy.factorial(3*k+1)) * (2**(12*k+6)))
    memo[n] = res
    return res

# Let's check the congruence for primes p >= 5
primes = [5, 7, 11, 13, 17, 19, 23, 29, 31]
for p in primes:
    for n in range(1, 5):
        for r in range(1, 3):
            # We want to check a(n * p^r) == a(n * p^(r-1)) (mod p^(3r))
            v1 = get_a(n * p**r)
            v2 = get_a(n * p**(r-1))
            mod = p**(3*r)
            diff = v1 - v2
            if diff % mod != 0:
                print(f"COUNTEREXAMPLE: p={p}, n={n}, r={r}")
                print(f"v1 = {v1}")
                print(f"v2 = {v2}")
                print(f"mod = {mod}")
                print(f"diff % mod = {diff % mod}")
                exit()
print("All checked cases are TRUE!")
