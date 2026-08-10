import sympy as sp
import math

import numpy as np
def choose(n, k):
    if k < 0 or k > n: return 0
    return math.comb(n, k)

def a(n):
    if n == 0: return 1
    r = n - 1
    s = 0
    for k in range(n + 1):
        s += choose(n, k) * choose(2*n + k - 1, r)
    return s

m = 7
# We have 2m = 14 coefficients for P and 14 for Q (plus leading coeff)
# So P has degree 14 (coeffs c0..c14)
# Q has degree 14 (coeffs d0..d14)
c = sp.symbols('c0:15')
d = sp.symbols('d0:15')
vars = c + d

# We generate recurrence equations for n=1..22 (we need 15+7=22 equations)
eqs = []
for n in range(1, 23):
    plus = 1
    for k in range(1, 2*m + 1):
        plus *= (2*m*n + k)
    minus = 1
    for k in range(1, 2*m + 1):
        minus *= (2*m*n - k)
    eq = plus * sum(c[i] * n**i for i in range(2*m+1)) * a(m*(n+1)) + \
         ((-1)**m) * minus * sum(c[i] * (-n)**i for i in range(2*m+1)) * a(m*(n-1)) - \
         sum(d[i] * n**(2*i) for i in range(2*m+1)) * a(m*n)
    eqs.append(sp.expand(eq))

# Symmetry equations P(x) = P(1-x) for x = 1..7 (since degree is 14)
for k in range(1, 8):
    eq = sum(c[i] * k**i for i in range(2*m+1)) - sum(c[i] * (1-k)**i for i in range(2*m+1))
    eqs.append(sp.expand(eq))

# Solve the system
print("Number of equations:", len(eqs))
# We set d14 = 1
eqs_subs = [eq.subs(d[14], 1) for eq in eqs]
sol = sp.solve(eqs_subs, vars[:-1])
print("Is system solvable?", len(sol) > 0)
if len(sol) > 0:
    print("Found solution!")
    # Get Q(x)
    Q_coeffs = [sol[d[i]] if d[i] in sol else (1 if i == 14 else 0) for i in range(15)]
    P_coeffs = [sol[c[i]] if c[i] in sol else 0 for i in range(15)]
    print("P coeffs:", P_coeffs)
    P_num = [float(c) for c in P_coeffs]
    num_roots_P = np.roots(P_num[::-1])
    print("Numerical roots of P:")
    for r in num_roots_P:
        print(r)

    print("Q coeffs:", Q_coeffs)
    # Check roots of Q(x)
    x = sp.Symbol('x')
    Q = sum(Q_coeffs[i] * x**i for i in range(15))
    roots = sp.solve(Q, x)
    print("Roots of Q:", roots)
    # Numerical roots of Q
    import numpy as np
    Q_num = [float(c) for c in Q_coeffs]
    # np.roots expects highest degree first
    num_roots = np.roots(Q_num[::-1])
    print("Numerical roots of Q:")
    for r in num_roots:
        print(r)
