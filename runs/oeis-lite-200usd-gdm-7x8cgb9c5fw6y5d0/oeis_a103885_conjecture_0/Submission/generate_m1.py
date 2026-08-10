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
    return a(1*n)  # m = 1

# m = 1, degree is 2.
# c0, c1, c2 (3 variables)
# d0, d1, d2 (3 variables)
# Total 6 variables. Set d2 = 1.
c = sp.symbols('c0:3')
d = sp.symbols('d0:3')
vars = c + d

# Symmetries: P(x) = P(1-x). 
# For k = 1: P(1) = P(0).
# P(x) = c0 + c1*x + c2*x^2
# P(1) - P(0) = c1 + c2 = 0.
eqs = []
# 5 recurrence equations (n = 1, 2, 3, 4, 5)
for n in range(1, 6):
    plus = (2 * n + 1) * (2 * n + 2)
    minus = (2 * n - 1) * (2 * n - 2)
    eq = plus * sum(c[i] * n**i for i in range(3)) * b(n+1) - minus * sum(c[i] * (-n)**i for i in range(3)) * b(n-1) - sum(d[i] * n**(2*i) for i in range(3)) * b(n)
    eqs.append(sp.expand(eq))

# Symmetry equation
eq_symm = sum(c[i] * 1**i for i in range(3)) - sum(c[i] * 0**i for i in range(3))
eqs.append(sp.expand(eq_symm))

# Let's solve the system of first 5 equations with d2 = 1
eqs_subs = [eq.subs(d[2], 1) for eq in eqs[:-1]]
sol = sp.solve(eqs_subs, vars[:-1])
print("Solution:", sol)
for idx, eq in enumerate(eqs):
    print(f"Eq {idx} value:", eq.subs(d[2], 1).subs(sol))


# Now check if the last equation (symmetry) is satisfied
if sol:
    symm_val = eq_symm.subs(d[2], 1).subs(sol)
    print("Symmetry equation value (should be non-zero for contradiction):", symm_val)
