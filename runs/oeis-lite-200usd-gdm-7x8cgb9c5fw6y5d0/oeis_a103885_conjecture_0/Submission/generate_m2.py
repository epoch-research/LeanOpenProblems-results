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
# Total 10 variables. Set d4 = 1.
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
    eqs.append(sp.expand(eq))

# Symmetry equations (k = 1, 2)
eqs_symm = []
for k in range(1, 3):
    eq_symm = sum(c[i] * k**i for i in range(5)) - sum(c[i] * (1 - k)**i for i in range(5))
    eqs_symm.append(sp.expand(eq_symm))

# Let's solve the system of first 8 recurrence + 1 symmetry equations with d4 = 1
eqs_to_solve = [eq.subs(d[4], 1) for eq in eqs] + [eqs_symm[0]]
sol = sp.solve(eqs_to_solve, vars[:-1])
print("Solution:", sol)

if sol:
    symm_val = eqs_symm[1].subs(d[4], 1).subs(sol)
    print("Symmetry 2 equation value:", symm_val)
