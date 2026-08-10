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

m = 13
c = sp.symbols(f'c0:{2*m+1}')
d = sp.symbols(f'd0:{2*m+1}')
vars = c + d

# We need 40 recurrence equations and 13 symmetry equations
eqs = []
for n in range(1, 41):
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

# Total equations: 53
eqs_subs = [eq.subs(d[2*m], 1) for eq in eqs]
sol = sp.solve(eqs_subs, vars[:-1])

if len(sol) > 0:
    print("Solution found!")
    c_vals = [sol.get(c[i], 0) for i in range(2*m+1)]
    d_vals = [sol.get(d[i], 0) for i in range(2*m)] + [1]
    
    import mpmath as mp
    mp.mp.dps = 100
    
    c_float = []
    for x in c_vals:
         try:
              c_float.append(float(sp.N(x)))
         except:
              c_float.append(0.0)
    d_float = []
    for x in d_vals:
         try:
              d_float.append(float(sp.N(x)))
         except:
              d_float.append(0.0)
              
    import numpy as np
    P_roots = np.roots(c_float[::-1])
    Q_roots = np.roots(d_float[::-1])
    print("P roots:")
    for r in P_roots:
         print(r)
    print("Q roots:")
    for r in Q_roots:
         print(r)
else:
    print("No solution found!")
