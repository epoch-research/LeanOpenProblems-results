import sympy
from sympy import binomial
from sympy.abc import x

for n in range(1, 100):
    P = sum((binomial(2*k, k)**2) * x**k for k in range(n + 1))
    Q = sum((binomial(2*k, k)**2) // (k + 1) * x**k for k in range(n + 1))
    
    if not sympy.factor(P) == P:
        print(f"P_{n} is reducible!")
    if not sympy.factor(Q) == Q:
        print(f"Q_{n} is reducible!")
print("Sympy done.")
