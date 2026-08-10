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

m = 11
print(f"Solving for m = {m}...")
c = sp.symbols(f'c0:{2*m+1}')
d = sp.symbols(f'd0:{2*m+1}')
vars = c + d

eqs = []
for n in range(1, 3*m + 2):
    plus = 1
    for k in range(1, 2*m + 1):
        plus *= (2*m*n + k)
    minus = 1
    for k in range(1, 2*m + 1):
        minus *= (2*m*n - k)
    eq = plus * sum(c[i] * n**i for i in range(2*m+1)) * a(m*(n+1)) + \
         ((-1)**m) * minus * sum(c[i] * (-n)**i for i in range(2*m+1)) * a(m*(n-1)) - \
         sum(d[i] * n**(2*i) for i in range(2*m+1)) * a(m*n)
    eqs.append(sp.expand(eq))

for k in range(1, m + 1):
    eq = sum(c[i] * k**i for i in range(2*m+1)) - sum(c[i] * (1-k)**i for i in range(2*m+1))
    eqs.append(sp.expand(eq))

eqs_subs = [eq.subs(d[2*m], 1) for eq in eqs]
sol = sp.solve(eqs_subs, vars[:-1])

if len(sol) > 0:
    c_vals = [sol.get(c[i], 0) for i in range(2*m+1)]
    # scale so that c_vals are integers or nice fractions
    # Let's print the coefficients of P
    print("Coefficients of P (c_0 to c_22):")
    for idx, val in enumerate(c_vals):
        print(f"c_{idx} = {val}")
    
    # Check 20-th derivative discriminant:
    # P^(20) = 20! * c_20 + 21! * c_21 * x + 22!/2 * c_22 * x^2
    # we can scale it to c_20 + 21 * c_21 * x + 231 * c_22 * x^2
    c20, c21, c22 = c_vals[20], c_vals[21], c_vals[22]
    D = 441 * c21**2 - 924 * c22 * c20
    print(f"20-th derivative (quadratic) discriminant: {D}")
    print(f"Float value of discriminant: {float(sp.N(D))}")
else:
    print("No solution found!")
