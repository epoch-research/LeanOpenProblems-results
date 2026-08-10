import sympy
from sympy import gamma, S, prime, isprime

def a(n):
    n_r = S(n)
    num = gamma(9 * n_r + 1) * gamma(2 * n_r + 1) * gamma(S(3)/2 * n_r + 1)
    den = gamma(S(9)/2 * n_r + 1) * gamma(4 * n_r + 1) * gamma(3 * n_r + 1) * gamma(n_r + 1)
    return num / den

def check_congruence(p, n, r):
    val1 = a(n * p**r)
    val2 = a(n * p**(r-1))
    mod = p**(3*r)
    diff = val1 - val2
    is_cong = (diff % mod) == 0
    print(f"p={p}, n={n}, r={r}: {is_cong} (diff = {diff}, mod = {mod})")
    return is_cong

# Let's check some primes
for p in [5, 7, 11, 13]:
    for n in range(1, 10):
        for r in [1, 2]:
            check_congruence(p, n, r)
