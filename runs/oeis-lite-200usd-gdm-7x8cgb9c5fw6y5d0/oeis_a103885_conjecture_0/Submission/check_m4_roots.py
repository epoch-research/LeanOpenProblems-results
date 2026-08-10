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
    return a(4*n)

# We want P of degree 2m = 8, Q of degree 2m = 8.
# So we have 9 coefficients for P and 9 for Q, total 18 variables.
c = sp.symbols('c0:9')
d = sp.symbols('d0:9')
vars = c + d

# We need at least 18 equations.
# Let's take recurrence for n = 1..16 (16 equations), and symmetry equations for P.
eqs_rec = []
for n in range(1, 17):
    plus = 1
    for k in range(1, 9):
        plus *= (8 * n + k)
    minus = 1
    for k in range(1, 9):
        minus *= (8 * n - k)
    P_pos = sum(c[i] * n**i for i in range(9))
    P_neg = sum(c[i] * (-n)**i for i in range(9))
    Q_val = sum(d[i] * (n**2)**i for i in range(9))
    eq = plus * P_pos * b(n+1) + minus * P_neg * b(n-1) - Q_val * b(n) # (-1)^4 = 1
    eqs_rec.append(sp.expand(eq))

eqs_symm = []
for k in range(1, 5):
    P_k = sum(c[i] * k**i for i in range(9))
    P_1_k = sum(c[i] * (1 - k)**i for i in range(9))
    eqs_symm.append(sp.expand(P_k - P_1_k))

M = sp.Matrix([[eq.coeff(v) for v in vars] for eq in eqs_rec + eqs_symm])
print("Matrix rank:", M.rank())
print("Nullspace dim:", len(M.nullspace()))

if M.nullspace():
    sol_vec = M.nullspace()[0]
    # Scale to integer
    denoms = [val.q for val in sol_vec if hasattr(val, 'q')]
    lcm = sp.lcm(denoms) if denoms else 1
    sol_int = sol_vec * lcm
    
    x = sp.Symbol('x')
    y = sp.Symbol('y')
    P = sum(sol_int[i] * x**i for i in range(9))
    Q = sum(sol_int[9+i] * y**i for i in range(9))
    
    # Check roots
    roots_P = sp.solve(P, x)
    print("Roots of P:")
    for r in roots_P:
        print(f"  {r.evalf()}")
        
    roots_Q = sp.solve(Q, y)
    print("Roots of Q:")
    for r in roots_Q:
        print(f"  {r.evalf()}")
