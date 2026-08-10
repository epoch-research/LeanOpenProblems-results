import sympy
from sympy import gamma, S

def a(n):
    n_r = S(n)
    num = gamma(9 * n_r + 1) * gamma(2 * n_r + 1) * gamma(S(3)/2 * n_r + 1)
    den = gamma(S(9)/2 * n_r + 1) * gamma(4 * n_r + 1) * gamma(3 * n_r + 1) * gamma(n_r + 1)
    return num / den

print("a(25) =", a(25))
print("a(5) =", a(5))
diff = a(25) - a(5)
print("diff % 5^6 =", diff % (5**6))

val1 = a(125)
val2 = a(25)
diff2 = val1 - val2
print("diff2 % 5^9 =", diff2 % (5**9))
