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

m = 5
c = sp.symbols('c0:11')
d = sp.symbols('d0:11')
vars = c + d

eqs = []
for n in range(1, 17):
    plus = 1
    for k in range(1, 11):
        plus *= (10*n + k)
    minus = 1
    for k in range(1, 11):
        minus *= (10*n - k)
    eq = plus * sum(c[i] * n**i for i in range(11)) * a(m*(n+1)) - minus * sum(c[i] * (-n)**i for i in range(11)) * a(m*(n-1)) - sum(d[i] * n**(2*i) for i in range(11)) * a(m*n)
    eqs.append(eq)

for k in range(1, 6):
    eq = sum(c[i] * k**i for i in range(11)) - sum(c[i] * (1 - k)**i for i in range(11))
    eqs.append(eq)

eqs_subs = [eq.subs(d[10], 1) for eq in eqs]
sol = sp.solve(eqs_subs, vars[:-1])

c0_vals = [sol[c[j]] for j in range(11)]
d0_vals = [sol[d[j]] for j in range(10)] + [1]

x = sp.Symbol('x')
P_poly = sum(c0_vals[j] * x**j for j in range(11))
Q_poly = sum(d0_vals[j] * x**j for j in range(11))

# Check roots of P
print("Checking roots of P...")
roots_P = sp.real_roots(P_poly)
print(f"Number of real roots of P: {len(roots_P)} / 10")
for r in roots_P:
    print(r.evalf())
    
# Check roots of Q
print("Checking roots of Q...")
roots_Q = sp.real_roots(Q_poly)
print(f"Number of real roots of Q: {len(roots_Q)} / 10")
for r in roots_Q:
    print(r.evalf())
