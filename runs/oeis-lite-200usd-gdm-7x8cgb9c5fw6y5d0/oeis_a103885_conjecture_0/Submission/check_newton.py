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
    
    # We want to express P(x) = sum_{i=0}^{22} c_i x^i as R(x(1-x)) = sum_{j=0}^{11} e_j (x(1-x))^j
    # Let's find e_j using sympy.
    x = sp.Symbol('x')
    P_expr = sum(c_vals[i] * x**i for i in range(2*m+1))
    # Since P(x) is symmetric about 1/2, it can be written as a polynomial in y = x(1-x).
    # Let's do a change of variable: x(1-x) = y => x^2 - x + y = 0 => x = (1 - sqrt(1 - 4y))/2.
    # Alternatively, we can just solve for e_j by matching coefficients of P(x) and R(x(1-x))
    e = sp.symbols(f'e0:{m+1}')
    R_expr = sum(e[j] * (x*(1-x))**j for j in range(m+1))
    diff_expr = sp.expand(P_expr - R_expr)
    e_sol = sp.solve([diff_expr.coeff(x, k) for k in range(2*m+1)], e)
    
    e_vals = [e_sol.get(e[j], 0) for j in range(m+1)]
    print("Coefficients of R(y) (e_0 to e_11):")
    for j, val in enumerate(e_vals):
        print(f"e_{j} = {val}")
        
    # Check Newton's inequalities:
    # e_k^2 >= e_{k-1} * e_{k+1} * (k+1)/k * (n-k+1)/(n-k)
    # here n = 11.
    n = 11
    print("\nChecking Newton's inequalities:")
    for k in range(1, n):
        lhs = e_vals[k]**2
        rhs = e_vals[k-1] * e_vals[k+1] * (k+1)/k * (n-k+1)/(n-k)
        diff = lhs - rhs
        is_ok = diff >= 0
        print(f"k = {k}: lhs = {float(sp.N(lhs)):.4e}, rhs = {float(sp.N(rhs)):.4e}, ok? {is_ok} (diff = {float(sp.N(diff)):.4e})")
else:
    print("No solution found!")
