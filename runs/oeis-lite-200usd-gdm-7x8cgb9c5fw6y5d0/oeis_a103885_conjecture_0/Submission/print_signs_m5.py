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
    return a(5*n)

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
    eq = plus * sum(c[i] * n**i for i in range(11)) * b(n+1) - minus * sum(c[i] * (-n)**i for i in range(11)) * b(n-1) - sum(d[i] * n**(2*i) for i in range(11)) * b(n)
    eqs.append(eq)

for k in range(1, 6):
    eq = sum(c[i] * k**i for i in range(11)) - sum(c[i] * (1 - k)**i for i in range(11))
    eqs.append(eq)

eqs_subs = [eq.subs(d[10], 1) for eq in eqs]
sol = sp.solve(eqs_subs, vars[:-1])

d0_vals = {j: sol[d[j]] for j in range(10)}
d0_vals[10] = 1

Q0_1_1 = sum(d0_vals[j] * (sp.Rational(11, 10))**j for j in range(11))
Q0_1_2 = sum(d0_vals[j] * (sp.Rational(12, 10))**j for j in range(11))

print("Q0_1_1:", Q0_1_1)
print("Float Q0_1_1:", float(Q0_1_1))
print("Q0_1_2:", Q0_1_2)
print("Float Q0_1_2:", float(Q0_1_2))
