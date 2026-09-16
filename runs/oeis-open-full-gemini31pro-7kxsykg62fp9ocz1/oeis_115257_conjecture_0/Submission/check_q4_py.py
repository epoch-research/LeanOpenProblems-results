import sympy
from sympy import binomial
from sympy.abc import x

Q4 = sum((binomial(2*k, k)**2) // (k + 1) * x**k for k in range(5))
print("Q4 =", Q4)
factors = sympy.factor(Q4)
print("Factors of Q4:", factors)
