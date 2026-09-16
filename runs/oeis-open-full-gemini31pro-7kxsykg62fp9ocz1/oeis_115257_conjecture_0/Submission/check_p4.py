import sympy
from sympy import binomial
from sympy.abc import x

P4 = sum((binomial(2*k, k)**2) * x**k for k in range(5))
print("P4 =", P4)
factors = sympy.factor(P4)
print("Factors of P4:", factors)
