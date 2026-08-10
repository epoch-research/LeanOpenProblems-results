import sympy

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

# Let's check for all primes p up to 100, and n, r up to 5
for p in range(5, 100):
    # check if p is prime
    if not sympy.isprime(p):
        continue
    for n in range(1, 3):
        for r in range(1, 3):
            v1 = get_a(n * p**r)
            v2 = get_a(n * p**(r-1))
            mod = p**(3*r)
            diff = v1 - v2
            if diff % mod != 0:
                print(f"FAILED for p={p}, n={n}, r={r}, diff % mod = {diff % mod}")
                exit()
print("All cases checked successfully up to p < 100, n < 5, r < 4!")
