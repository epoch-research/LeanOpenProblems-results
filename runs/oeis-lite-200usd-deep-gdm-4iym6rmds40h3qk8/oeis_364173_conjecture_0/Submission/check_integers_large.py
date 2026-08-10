import sympy
from sympy import gamma, S

def a(n):
    n_r = S(n)
    num = gamma(9 * n_r + 1) * gamma(2 * n_r + 1) * gamma(S(3)/2 * n_r + 1)
    den = gamma(S(9)/2 * n_r + 1) * gamma(4 * n_r + 1) * gamma(3 * n_r + 1) * gamma(n_r + 1)
    return num / den

print("Checking integrality of a(n) up to n = 500...")
for n in range(500):
    val = a(n)
    if not val.is_integer:
        print(f"FOUND NON-INTEGER: a({n}) = {val}")
        break
else:
    print("All checked a(n) are integers!")
