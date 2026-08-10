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

# Recurrences: rec_n
# plus_n * P(n) * b(n+1) - minus_n * P(-n) * b(n-1) - Q(n^2) * b(n)
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
    
    eq = plus * P_pos * b(n+1) - minus * P_neg * b(n-1) - Q_val * b(n)
    eqs_rec.append(sp.expand(eq))

# Symmetries: symm_k
# P(k) - P(1-k)
eqs_symm = []
for k in range(1, 3):
    P_k = sum(c[i] * k**i for i in range(5))
    P_1_k = sum(c[i] * (1 - k)**i for i in range(5))
    eq_symm = P_k - P_1_k
    eqs_symm.append(sp.expand(eq_symm))

# Weights
w = sp.symbols('w1:9')
u = sp.symbols('u1:3')
weights = w + u

# We want sum(w_i * rec_i) + sum(u_k * symm_k) = -d4
# Let's group by c0..c4, d0..d4
target = -d[4]

equations = []
for v in vars:
    coeff_lhs = sum(w[i-1] * eqs_rec[i-1].coeff(v) for i in range(1, 9)) + sum(u[k-1] * eqs_symm[k-1].coeff(v) for k in range(1, 3))
    equations.append(coeff_lhs - target.coeff(v))

sol = sp.solve(equations, weights)
print("Weights solution:")
for k, v in sol.items():
    print(f"{k}: {v}")
