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

# For m=1:
# A103885_subsequence_real 1 n = a(n)
# prod_factor_plus 1 n = (2n + 1)(2n + 2)
# prod_factor_minus 1 n = (2n - 1)(2n - 2)
# P(x) = 5x^2 - 5x + 1
# Q(y) = 220y^2 - 136y + 12

P = lambda x: 5*x**2 - 5*x + 1
Q = lambda y: 220*y**2 - 136*y + 12

for n in range(1, 6):
    plus = (2*n + 1)*(2*n + 2)
    minus = (2*n - 1)*(2*n - 2)
    
    LHS = plus * P(n) * a(n+1) - minus * P(-n) * a(n-1)
    RHS = Q(n**2) * a(n)
    
    print(f"n = {n}:")
    print(f"  LHS = {LHS}")
    print(f"  RHS = {RHS}")
    print(f"  LHS == RHS: {LHS == RHS}")
