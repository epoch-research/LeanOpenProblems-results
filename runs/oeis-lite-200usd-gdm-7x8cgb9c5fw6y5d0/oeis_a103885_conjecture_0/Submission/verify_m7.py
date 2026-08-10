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
    return a(7*n)

m = 7
c = sp.symbols('c0:15')
d = sp.symbols('d0:15')
vars = c + d

# Solve the system with 22 recurrence equations and 7 symmetry equations
eqs = []
for n in range(1, 23):
    plus = 1
    for k in range(1, 15):
        plus *= (14*n + k)
    minus = 1
    for k in range(1, 15):
        minus *= (14*n - k)
    eq = plus * sum(c[i] * n**i for i in range(15)) * b(n+1) - \
         minus * sum(c[i] * (-n)**i for i in range(15)) * b(n-1) - \
         sum(d[i] * n**(2*i) for i in range(15)) * b(n)
    eqs.append(sp.expand(eq))

for k in range(1, 8):
    eq = sum(c[i] * k**i for i in range(15)) - sum(c[i] * (1-k)**i for i in range(15))
    eqs.append(sp.expand(eq))

eqs_subs = [eq.subs(d[14], 1) for eq in eqs]
sol = sp.solve(eqs_subs, vars[:-1])
sol_dict = {k: v for k, v in sol.items()}
sol_dict[d[14]] = 1

# Check for n = 23, 24, 25
for n in [23, 24, 25]:
    plus = 1
    for k in range(1, 15):
        plus *= (14*n + k)
    minus = 1
    for k in range(1, 15):
        minus *= (14*n - k)
    
    P_pos = sum(sol_dict[c[i]] * n**i for i in range(15))
    P_neg = sum(sol_dict[c[i]] * (-n)**i for i in range(15))
    Q_val = sum(sol_dict[d[i]] * (n**2)**i for i in range(15))
    
    eq = plus * P_pos * b(n+1) - minus * P_neg * b(n-1) - Q_val * b(n)
    print(f"n = {n}: eq value = {eq.subs(sol_dict)}")
