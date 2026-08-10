import sympy
from sympy import gamma, S

def a(n):
    n_r = S(n)
    num = gamma(9 * n_r + 1) * gamma(2 * n_r + 1) * gamma(S(3)/2 * n_r + 1)
    den = gamma(S(9)/2 * n_r + 1) * gamma(4 * n_r + 1) * gamma(3 * n_r + 1) * gamma(n_r + 1)
    return num / den

for p in [5, 7]:
    for n in [1, 2]:
        for r in [1, 2]:
            val1 = a(n * p**r)
            val2 = a(n * p**(r-1))
            diff = val1 - val2
            mod = p**(3*r)
            quot = diff / mod
            print(f"p={p}, n={n}, r={r}: quotient = {quot}")
