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

M = sp.Matrix([[eq.coeff(v) for v in vars] for eq in eqs_rec + eqs_symm])
ns = M.nullspace()
if ns:
    sol_vec = ns[0]
    # Let's scale it so that the entries are integers
    # Find the least common multiple of denominators
    denoms = [val.q for val in sol_vec if hasattr(val, 'q')]
    lcm = sp.lcm(denoms)
    sol_int = sol_vec * lcm
    
    print("Integer solution:")
    for v, val in zip(vars, sol_int):
        print(f"{v}: {val}")
        
    # Let's print P and Q
    x = sp.Symbol('x')
    y = sp.Symbol('y')
    P = sum(sol_int[i] * x**i for i in range(5))
    Q = sum(sol_int[5+i] * y**i for i in range(5))
    print("P(x) =", P)
    print("Q(y) =", Q)
else:
    print("No solution found in nullspace")
