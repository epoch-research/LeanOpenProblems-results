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

m = 11
print(f"Solving for m = {m}...")
c = sp.symbols(f'c0:{2*m+1}')
d = sp.symbols(f'd0:{2*m+1}')
vars = c + d

eqs = []
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
    c_vals = [sol.get(c[i], 0) for i in range(2*m+1)]
    x = sp.Symbol('x')
    P_expr = sum(c_vals[i] * x**i for i in range(2*m+1))
    
    print("Finding real roots of P(x)...")
    roots = sp.real_roots(P_expr)
    print(f"Number of real roots: {len(roots)}")
    for idx, r in enumerate(roots):
         print(f"Root {idx}: {r.evalf()}")
else:
    print("No solution found!")
