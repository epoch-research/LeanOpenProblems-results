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

# We will search m from 1 to 20
for m in range(1, 21):
    c = sp.symbols(f'c0:{2*m+1}')
    d = sp.symbols(f'd0:{2*m+1}')
    vars = c + d

    # We need 2*m + 1 recurrence equations and m symmetry equations, total 3*m + 1 equations
    # Wait, we have 4*m + 2 variables, so we need at least that many equations.
    # Let's generate 3*m recurrence equations and m symmetry equations.
    eqs = []
    # Recurrence equations
    for n in range(1, 3*m + 1):
        plus = 1
        for k in range(1, 2*m + 1):
            plus *= (2*m*n + k)
        minus = 1
        for k in range(1, 2*m + 1):
            minus *= (2*m*n - k)
        # Note the sign (-1)^m
        eq = plus * sum(c[i] * n**i for i in range(2*m+1)) * a(m*(n+1)) + \
             ((-1)**m) * minus * sum(c[i] * (-n)**i for i in range(2*m+1)) * a(m*(n-1)) - \
             sum(d[i] * n**(2*i) for i in range(2*m+1)) * a(m*n)
        eqs.append(sp.expand(eq))

    # Symmetry equations
    for k in range(1, m + 1):
        eq = sum(c[i] * k**i for i in range(2*m+1)) - sum(c[i] * (1-k)**i for i in range(2*m+1))
        eqs.append(sp.expand(eq))

    eqs_subs = [eq.subs(d[2*m], 1) for eq in eqs]
    sol = sp.solve(eqs_subs, vars[:-1])
    if len(sol) > 0:
        P_coeffs = [sol[c[i]] if c[i] in sol else 0 for i in range(2*m+1)]
        Q_coeffs = [sol[d[i]] if d[i] in sol else (1 if i == 2*m else 0) for i in range(2*m+1)]
        
        P_float = []
        for x in P_coeffs[::-1]:
            try:
                P_float.append(float(x.evalf()))
            except:
                P_float.append(0.0)
        P_roots = np.roots(P_float)
        P_ok = True
        for r in P_roots:
            if abs(r.imag) > 1e-5 or r.real < -1e-5 or r.real > 1 + 1e-5:
                P_ok = False
                break
        
        Q_float = []
        for x in Q_coeffs[::-1]:
            try:
                Q_float.append(float(x.evalf()))
            except:
                Q_float.append(0.0)
        Q_roots = np.roots(Q_float)
        Q_ok = True
        for r in Q_roots:
            if abs(r.imag) > 1e-5 or r.real < -1e-5 or r.real > 1 + 1e-5:
                Q_ok = False
                break
                
        print(f"m = {m}: Solved. P roots OK: {P_ok}, Q roots OK: {Q_ok}")
        if not P_ok or not Q_ok:
            print(f"  P roots: {P_roots}")
            print(f"  Q roots: {Q_roots}")
    else:
        print(f"m = {m}: No solution")
