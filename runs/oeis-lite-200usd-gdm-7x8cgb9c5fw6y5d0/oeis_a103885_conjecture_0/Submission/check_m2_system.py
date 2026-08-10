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
    return a(2*n)

# Let's print values of b(n) for n = 0..10
for n in range(11):
    print(f"b({n}) = {b(n)}")

c = sp.symbols('c0:5')
d = sp.symbols('d0:5')
vars = c + d

eqs_rec = []
for n in range(1, 9):
    plus = 1
    for k in range(1, 5):
        plus *= (4 * n + k)
    minus = 1
    for k in range(1, 5):
        minus *= (4 * n - k)
    P_pos = sum(c[i] * n**i for i in range(5))
    P_neg = sum(c[i] * (-n)**i for i in range(5))
    Q_val = sum(d[i] * (n**2)**i for i in range(5))
    eq = plus * P_pos * b(n+1) + minus * P_neg * b(n-1) - Q_val * b(n)
    eqs_rec.append(sp.expand(eq))

eqs_symm = []
for k in range(1, 3):
    P_k = sum(c[i] * k**i for i in range(5))
    P_1_k = sum(c[i] * (1 - k)**i for i in range(5))
    eq_symm = P_k - P_1_k
    eqs_symm.append(sp.expand(eq_symm))

# Construct the matrix of the homogeneous system of equations in c and d
M = sp.Matrix([[eq.coeff(v) for v in vars] for eq in eqs_rec + eqs_symm])
print("Matrix rank:", M.rank())
print("Number of variables:", len(vars))
print("Nullspace dimension:", len(M.nullspace()))
