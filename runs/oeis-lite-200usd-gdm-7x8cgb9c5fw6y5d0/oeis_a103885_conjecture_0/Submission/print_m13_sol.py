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
    return a(13*n)

m = 13
c = sp.symbols(f'c0:{2*m+1}')
d = sp.symbols(f'd0:{2*m+1}')
vars = c + d

eqs = []
for n in range(1, 3*m + 1):
    plus = 1
    for k in range(1, 2*m + 1):
        plus *= (2*m*n + k)
    minus = 1
    for k in range(1, 2*m + 1):
        minus *= (2*m*n - k)
    eq = plus * sum(c[i] * n**i for i in range(2*m+1)) * b(n+1) + \
         ((-1)**m) * minus * sum(c[i] * (-n)**i for i in range(2*m+1)) * b(n-1) - \
         sum(d[i] * n**(2*i) for i in range(2*m+1)) * b(n)
    eqs.append(sp.expand(eq))

for k in range(1, m + 1):
    eq = sum(c[i] * k**i for i in range(2*m+1)) - sum(c[i] * (1-k)**i for i in range(2*m+1))
    eqs.append(sp.expand(eq))

eqs_subs = [eq.subs(d[2*m], 1) for eq in eqs]
sol = sp.solve(eqs_subs, vars[:-1])

print("type of sol:", type(sol))
if isinstance(sol, dict):
    print("keys in sol:", len(sol))
    # print symbols that are not in sol
    missing = [v for v in vars[:-1] if v not in sol]
    print("missing symbols:", missing)
elif isinstance(sol, list):
    print("len of sol:", len(sol))
    if len(sol) > 0:
        print("type of first element:", type(sol[0]))
