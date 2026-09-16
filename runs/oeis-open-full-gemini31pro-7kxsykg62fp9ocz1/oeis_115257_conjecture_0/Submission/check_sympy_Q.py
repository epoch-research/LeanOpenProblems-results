import sympy
from sympy import binomial
from sympy.abc import x

for n in range(1, 40):
    Q = sum((binomial(2*k, k)**2) // (k + 1) * x**k for k in range(n + 1))
    
    fac = sympy.factor(Q)
    if fac != Q:
        print(f"Q_{n} reducible: {fac}")
print("Sympy done.")
