import math
from sympy import gamma, S

def a(n):
    # Using SymPy for exact rational arithmetic
    n_r = S(n)
    num = gamma(9 * n_r + 1) * gamma(2 * n_r + 1) * gamma(S(3)/2 * n_r + 1)
    den = gamma(S(9)/2 * n_r + 1) * gamma(4 * n_r + 1) * gamma(3 * n_r + 1) * gamma(n_r + 1)
    val = num / den
    return val

for n in range(100):
    val = a(n)
    is_int = val.is_integer
    print(f"a({n}) = {val} (is integer: {is_int})")
