import sympy as sp
import math
import numpy as np

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
    return a(4*n)

# We solve the system using sympy for the coefficients
c = sp.symbols('c0:9')
d = sp.symbols('d0:9')
vars = c + d

eqs_rec = []
for n in range(1, 15): # 14 equations is enough since nullspace is dim 1
    plus = 1
    for k in range(1, 9):
        plus *= (8 * n + k)
    minus = 1
    for k in range(1, 9):
        minus *= (8 * n - k)
    P_pos = sum(c[i] * n**i for i in range(9))
    P_neg = sum(c[i] * (-n)**i for i in range(9))
    Q_val = sum(d[i] * (n**2)**i for i in range(9))
    eq = plus * P_pos * b(n+1) + minus * P_neg * b(n-1) - Q_val * b(n)
    eqs_rec.append(sp.expand(eq))

eqs_symm = []
for k in range(1, 5):
    P_k = sum(c[i] * k**i for i in range(9))
    P_1_k = sum(c[i] * (1 - k)**i for i in range(9))
    eqs_symm.append(sp.expand(P_k - P_1_k))

M = sp.Matrix([[eq.coeff(v) for v in vars] for eq in eqs_rec + eqs_symm])
ns = M.nullspace()
if ns:
    sol = ns[0]
    # convert to float list
    sol_float = [float(val.evalf()) for val in sol]
    
    # Polynomial P has coefficients sol_float[0:9]
    # Polynomial Q has coefficients sol_float[9:18]
    # numpy expects coefficients from highest to lowest degree
    coeffs_P = sol_float[0:9][::-1]
    coeffs_Q = sol_float[9:18][::-1]
    
    roots_P = np.roots(coeffs_P)
    roots_Q = np.roots(coeffs_Q)
    
    print("Roots of P:")
    for r in roots_P:
        print(f"  {r}")
        
    print("Roots of Q:")
    for r in roots_Q:
        print(f"  {r}")
else:
    print("No nullspace found!")
