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

m = 3
c = sp.symbols('c0:7')
d = sp.symbols('d0:7')
vars = c + d

eqs = []
for n in range(1, 15):
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

for k in range(1, 4):
    eq = sum(c[i] * k**i for i in range(2*m+1)) - sum(c[i] * (1-k)**i for i in range(2*m+1))
    eqs.append(sp.expand(eq))

eqs_subs = [eq.subs(d[6], 1) for eq in eqs]
sol = sp.solve(eqs_subs, vars[:-1])
if len(sol) > 0:
    P_coeffs = [sol[c[i]] if c[i] in sol else 0 for i in range(7)]
    Q_coeffs = [sol[d[i]] if d[i] in sol else (1 if i == 6 else 0) for i in range(7)]
    print("P roots:")
    for r in np.roots([float(x) for x in P_coeffs[::-1]]):
        print(r)
    print("Q roots:")
    for r in np.roots([float(x) for x in Q_coeffs[::-1]]):
        print(r)
else:
    print("No solution")
