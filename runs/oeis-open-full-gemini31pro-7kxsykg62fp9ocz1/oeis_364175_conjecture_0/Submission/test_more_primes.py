import sys
sys.set_int_max_str_digits(2000000)
def a(n):
    num = 1
    den = 1
    for k in range(1, n+1):
        den *= (2*n + 3*k)
    import math
    num *= math.factorial(6*n) * (3**n)
    den *= math.factorial(3*n) * math.factorial(2*n)
    return num // den

primes = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
for p in primes:
    r = 1
    for n in range(1, 20):
        if a(n * p**r) % (p**(3*r)) != a(n * p**(r-1)) % (p**(3*r)):
            print(f"False for p={p}, r={r}, n={n}")
            sys.exit(0)
print("Checked primes up to 47 for r=1, n=1..19")
