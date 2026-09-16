import sympy
from sympy import binomial
from sympy.abc import x

for n in range(1, 40):
    P = sum((binomial(2*k, k)**2) * x**k for k in range(n + 1))
    
    fac = sympy.factor(P)
    if fac != P:
        print(f"P_{n} reducible: {fac}")
print("Sympy done.")
