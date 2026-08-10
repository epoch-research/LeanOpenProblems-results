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

x = sp.Symbol('x')
y = sp.Symbol('y')

# Our polynomials from the nullspace of the system for n=1..8
P = 110*x**4 - 220*x**3 + 148*x**2 - 38*x + 3
Q = 3463680*y**4 - 4551616*y**3 + 1696064*y**2 - 168064*y + 3456

for n in range(1, 12):
    plus = 1
    for k in range(1, 5):
        plus *= (4 * n + k)
    minus = 1
    for k in range(1, 5):
        minus *= (4 * n - k)
        
    P_pos = P.subs(x, n)
    P_neg = P.subs(x, -n)
    Q_val = Q.subs(y, n**2)
    
    lhs = plus * P_pos * b(n+1) + minus * P_neg * b(n-1)
    rhs = Q_val * b(n)
    
    print(f"n = {n}:")
    print(f"  LHS = {lhs}")
    print(f"  RHS = {rhs}")
    print(f"  LHS == RHS: {lhs == rhs}")
