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

def b(n):
    return a(3*n)

m = 3
c = sp.symbols('c0:7')
d = sp.symbols('d0:7')
vars = c + d

eqs = []
for n in range(1, 11):
    plus = 1
    for k in range(1, 7):
        plus *= (6*n + k)
    minus = 1
    for k in range(1, 7):
        minus *= (6*n - k)
    
    P_pos = sum(c[i] * n**i for i in range(7))
    P_neg = sum(c[i] * (-n)**i for i in range(7))
    Q_val = sum(d[i] * (n**2)**i for i in range(7))
    
    eq = plus * P_pos * b(n+1) - minus * P_neg * b(n-1) - Q_val * b(n)
    eqs.append(sp.expand(eq))

# Symmetry: P(k) - P(1-k) = 0 for k = 1..3
for k in range(1, 4):
    eq = sum(c[i] * k**i for i in range(7)) - sum(c[i] * (1-k)**i for i in range(7))
    eqs.append(sp.expand(eq))

# Total equations: 10 recurrence + 3 symmetry = 13 equations.
# Total variables: 14 (c0..c6, d0..d6). Let's set d6 = 1.
eqs_subs = [eq.subs(d[6], 1) for eq in eqs]
sol = sp.solve(eqs_subs, vars[:-1])

if len(sol) > 0:
    print("Solution found!")
    c_vals = [sol[c[i]] for i in range(7)]
    d_vals = [sol[d[i]] for i in range(6)] + [1]
    
    import numpy as np
    c_float = [float(sp.N(x)) for x in c_vals]
    d_float = [float(sp.N(x)) for x in d_vals]
    
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
