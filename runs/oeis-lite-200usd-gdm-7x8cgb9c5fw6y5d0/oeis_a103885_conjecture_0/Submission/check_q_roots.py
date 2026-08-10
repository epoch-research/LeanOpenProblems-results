import sympy as sp
import math

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

for m in range(1, 20):
    print(f"Checking m = {m}...")
    c = sp.symbols(f'c0:{2*m+1}')
    d = sp.symbols(f'd0:{2*m+1}')
    vars = c + d

    eqs = []
    # We need 3m+1 recurrence equations and m symmetry equations
    for n in range(1, 3*m + 2):
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

    for k in range(1, m + 1):
        eq = sum(c[i] * k**i for i in range(2*m+1)) - sum(c[i] * (1-k)**i for i in range(2*m+1))
        eqs.append(sp.expand(eq))

    eqs_subs = [eq.subs(d[2*m], 1) for eq in eqs]
    sol = sp.solve(eqs_subs, vars[:-1])

    if len(sol) > 0:
        d_vals = [sol.get(d[i], 0) for i in range(2*m)] + [1]
        
        import numpy as np
        d_float = [float(sp.N(x)) for x in d_vals]
        Q_roots = np.roots(d_float[::-1])
        
        Q_ok = True
        for r in Q_roots:
            if abs(r.imag) > 1e-4 or r.real < 0 or r.real > 1:
                Q_ok = False
                print(f"  Q Root violated for m = {m}: {r}")
                
        print(f"  m = {m}: Q roots OK: {Q_ok}")
    else:
        print("  No solution found!")
