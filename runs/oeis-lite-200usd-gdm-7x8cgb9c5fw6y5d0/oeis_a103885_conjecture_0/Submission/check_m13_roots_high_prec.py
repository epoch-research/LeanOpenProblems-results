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

eqs_subs = [eq.subs(d[2*m], 1) for eq in eqs]
sol = sp.solve(eqs_subs, vars[:-1])

if len(sol) > 0:
    print("Solution found!")
    c_vals = [sol.get(c[i], 0) for i in range(2*m+1)]
    
    import mpmath as mp
    mp.mp.dps = 200
    
    # Filter out coefficients that are sympy numbers
    c_mp = []
    for x in c_vals:
         if hasattr(x, 'p') and hasattr(x, 'q'):
              c_mp.append(mp.mpf(x.p) / mp.mpf(x.q))
         elif isinstance(x, int) or isinstance(x, sp.Integer):
              c_mp.append(mp.mpf(int(x)))
         else:
              c_mp.append(mp.mpf(float(x.evalf())))
              
    P_roots = mp.polyroots(c_mp[::-1])
    print("P roots with 200-digit precision:")
    for r in P_roots:
         print(r)
else:
    print("No solution found!")
