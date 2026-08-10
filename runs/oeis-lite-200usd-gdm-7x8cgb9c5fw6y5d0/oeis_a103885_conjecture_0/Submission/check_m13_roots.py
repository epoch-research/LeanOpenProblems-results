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

eqs = []
for n in range(1, 3*m + 1):
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

P_coeffs = [sol[c[i]] if c[i] in sol else 0 for i in range(2*m+1)]
Q_coeffs = [sol[d[i]] if d[i] in sol else (1 if i == 2*m else 0) for i in range(2*m+1)]

# Convert to mpmath
import mpmath as mp
mp.mp.dps = 200

P_mp = [mp.mpf(x.p) / mp.mpf(x.q) if hasattr(x, 'p') else mp.mpf(0) for x in P_coeffs]
Q_mp = [mp.mpf(x.p) / mp.mpf(x.q) if hasattr(x, 'p') else mp.mpf(0) for x in Q_coeffs]
# If any x is not rational but int:
for idx, x in enumerate(P_coeffs):
    if isinstance(x, int) or isinstance(x, sp.Integer):
        P_mp[idx] = mp.mpf(int(x))
for idx, x in enumerate(Q_coeffs):
    if isinstance(x, int) or isinstance(x, sp.Integer):
        Q_mp[idx] = mp.mpf(int(x))

P_roots = mp.polyroots(P_mp[::-1])
Q_roots = mp.polyroots(Q_mp[::-1])

print("P roots:")
for r in P_roots:
    print(r)
print("Q roots:")
for r in Q_roots:
    print(r)
