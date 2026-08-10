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

for m in range(1, 21):
    print(f"\nSolving for m = {m}...")
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
        d_vals = [sol.get(d[i], 0) for i in range(2*m)] + [1]
        
        # We find e_vals
        x = sp.Symbol('x')
        P_expr = sum(c_vals[i] * x**i for i in range(2*m+1))
        e = sp.symbols(f'e0:{m+1}')
        R_expr = sum(e[j] * (x*(1-x))**j for j in range(m+1))
        diff_expr = sp.expand(P_expr - R_expr)
        e_sol = sp.solve([diff_expr.coeff(x, k) for k in range(2*m+1)], e)
        
        y = sp.Symbol('y')
        R_poly = sum(e_sol.get(e[j], 0) * y**j for j in range(m+1))
        
        roots_R = sp.real_roots(R_poly)
        print(f"  R(y) real roots: {len(roots_R)} / {m}")
        if len(roots_R) < m:
            print(f"  FAILED: R(y) has non-real roots!")
            break
            
        all_lt_quarter = True
        for r in roots_R:
            if r.evalf() >= 0.25:
                all_lt_quarter = False
                print(f"  FAILED: R(y) root >= 0.25: {r.evalf()}")
        if not all_lt_quarter:
            break
            
        # Check Q roots
        w = sp.Symbol('w')
        Q_poly = sum(d_vals[i] * w**i for i in range(2*m+1))
        roots_Q = sp.real_roots(Q_poly)
        print(f"  Q(w) real roots: {len(roots_Q)} / {2*m}")
        if len(roots_Q) < 2*m:
            print(f"  FAILED: Q(w) has non-real roots!")
            break
            
        all_in_01 = True
        for r in roots_Q:
            val = r.evalf()
            if val < 0 or val > 1:
                all_in_01 = False
                print(f"  FAILED: Q(w) root not in [0,1]: {val}")
        if not all_in_01:
            break
            
        print("  ALL CONDITIONS SATISFIED!")
    else:
        print("  No solution found!")
        break
