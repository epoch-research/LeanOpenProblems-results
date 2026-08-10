from sympy import factorint
import sympy
from sympy import gamma, S

def a(n):
    n_r = S(n)
    num = gamma(9 * n_r + 1) * gamma(2 * n_r + 1) * gamma(S(3)/2 * n_r + 1)
    den = gamma(S(9)/2 * n_r + 1) * gamma(4 * n_r + 1) * gamma(3 * n_r + 1) * gamma(n_r + 1)
    return num / den

for n in range(1, 11):
    val = int(a(n))
    print(f"a({n}) = {val} = {factorint(val)}")
