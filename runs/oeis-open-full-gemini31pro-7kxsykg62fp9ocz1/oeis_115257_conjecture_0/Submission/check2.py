import sympy
from sympy import binomial
from sympy.abc import x

def check_irreducible(max_n):
    for n in range(1, max_n + 1):
        P = sum((binomial(2*k, k)**2) * x**k for k in range(n + 1))
        Q = sum((binomial(2*k, k)**2) / (k + 1) * x**k for k in range(n + 1))
        
        P_poly = sympy.Poly(P, x, domain='QQ')
        Q_poly = sympy.Poly(Q, x, domain='QQ')
        
        if not P_poly.is_irreducible:
            print(f"P_{n} is reducible!")
        if not Q_poly.is_irreducible:
            print(f"Q_{n} is reducible!")

check_irreducible(50)
print("Done")
