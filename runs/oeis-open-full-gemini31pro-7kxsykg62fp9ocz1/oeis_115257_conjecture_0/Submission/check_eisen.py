import sympy
from sympy import binomial
from sympy.abc import x

for n in range(1, 20):
    P = sum((binomial(2*k, k)**2) * x**k for k in range(n + 1))
    
    # check shift by c
    found = False
    for c in range(-20, 20):
        shifted = sympy.Poly(P.subs(x, x + c), x, domain='ZZ')
        # Check eisenstein
        coeffs = shifted.all_coeffs()
        a_n = coeffs[0]
        a_0 = coeffs[-1]
        for p in sympy.primefactors(a_0):
            if a_n % p == 0: continue
            valid = True
            for i in range(1, n+1):
                if coeffs[i] % p != 0:
                    valid = False
                    break
            if valid and a_0 % (p**2) != 0:
                print(f"P_{n} shifted by {c} is Eisenstein at {p}")
                found = True
                break
        if found: break
    if not found:
        print(f"P_{n} no shift works")
