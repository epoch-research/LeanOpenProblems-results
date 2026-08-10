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

# Coefficients from check_m2.py
c = [sp.Rational(1, 1154560), sp.Rational(-19, 1731840), sp.Rational(37, 865920), sp.Rational(-1, 15744), sp.Rational(1, 31488)]
d = [sp.Rational(9, 9020), sp.Rational(-1313, 27060), sp.Rational(26501, 54120), sp.Rational(-71119, 54120), sp.Rational(1, 1)]

for n in range(1, 10):
    plus = math.prod(4 * n + k for k in range(1, 5))
    minus = math.prod(4 * n - k for k in range(1, 5))
    
    P_pos = sum(c[i] * n**i for i in range(5))
    P_neg = sum(c[i] * (-n)**i for i in range(5))
    Q_val = sum(d[i] * (n**2)**i for i in range(5))
    
    LHS = plus * P_pos * b(n+1) + minus * P_neg * b(n-1)
    RHS = Q_val * b(n)
    print(f"n = {n}: LHS = {LHS}, RHS = {RHS}, Diff = {LHS - RHS}")
