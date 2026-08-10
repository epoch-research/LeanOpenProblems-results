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
    return a(2*n)  # m = 2

# m = 2, degree is 4.
# c0..c4 (5 variables)
# d0..d4 (5 variables)
# Set d4 = 1.
c = sp.symbols('c0:5')
d = sp.symbols('d0:5')
vars = c + d

eqs = []
# 8 recurrence equations (n = 1..8)
for n in range(1, 9):
    plus = 1
    for k in range(1, 5):
        plus *= (4 * n + k)
    minus = 1
    for k in range(1, 5):
        minus *= (4 * n - k)
    eq = plus * sum(c[i] * n**i for i in range(5)) * b(n+1) - minus * sum(c[i] * (-n)**i for i in range(5)) * b(n-1) - sum(d[i] * n**(2*i) for i in range(5)) * b(n)
    eqs.append(eq)

# Symmetry equations (k = 1, 2)
eqs_symm = []
for k in range(1, 3):
    eq_symm = sum(c[i] * k**i for i in range(5)) - sum(c[i] * (1 - k)**i for i in range(5))
    eqs_symm.append(eq_symm)

# We have 10 equations total: 8 recurrences, 2 symmetries
# Let's solve them with d4 = 1
all_eqs = [eq.subs(d[4], 1) for eq in eqs] + [eq.subs(d[4], 1) for eq in eqs_symm]
# Solve for c0..c4, d0..d3 (9 variables)
# Solve using the first 9 equations: 8 recurrences and 1st symmetry
eqs_subs = [eq.subs(d[4], 1) for eq in eqs] + [eqs_symm[0].subs(d[4], 1)]
sol = sp.solve(eqs_subs, vars[:-1])

d_vals = {j: sol[d[j]] for j in range(4)}
d_vals[4] = 1

# Q0 polynomial
x = sp.Symbol('x')
print("Q0 coefficients:")
for j in range(5):
    print(f"d{j} = {d_vals[j]}")

print("\nEvaluations:")
for i in range(11, 21):
    val = sum(d_val * (sp.Rational(i, 10))**j for j, d_val in d_vals.items())
    print(f"Q0({i}/10) = {float(val)} ({val})")
