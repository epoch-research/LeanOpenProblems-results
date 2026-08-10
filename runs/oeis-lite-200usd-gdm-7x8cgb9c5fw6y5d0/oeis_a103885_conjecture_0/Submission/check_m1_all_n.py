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

# For m = 1:
c0, c1, c2 = 1/220, -1/44, 1/44
d0, d1, d2 = 3/55, -34/55, 1

for n in range(1, 10):
    plus = (2 * n + 1) * (2 * n + 2)
    minus = (2 * n - 1) * (2 * n - 2)
    P_pos = c0 + c1 * n + c2 * n**2
    P_neg = c0 + c1 * (-n) + c2 * (-n)**2
    Q_val = d0 + d1 * n**2 + d2 * n**4
    
    LHS = plus * P_pos * a(n+1) - minus * P_neg * a(n-1)
    RHS = Q_val * a(n)
    print(f"n = {n}: LHS = {LHS}, RHS = {RHS}, Diff = {LHS - RHS}")
