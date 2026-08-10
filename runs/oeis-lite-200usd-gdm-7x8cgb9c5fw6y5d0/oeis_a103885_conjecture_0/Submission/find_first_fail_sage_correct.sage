def choose(n, k):
    if k < 0 or k > n: return 0
    return binomial(n, k)

def a(n):
    if n == 0: return 1
    r = n - 1
    s = 0
    for k in range(n + 1):
        s += choose(n, k) * choose(2*n + k - 1, r)
    return s

for m in range(1, 36):
    n_vars = 4 * m + 1
    
    b = [QQ(a(m*i)) for i in range(3*m + 3)]
    
    varnames = [f'c{i}' for i in range(2*m+1)] + [f'd{i}' for i in range(2*m)]
    ring = PolynomialRing(QQ, names=varnames)
    vars = list(ring.gens())
    
    eqs = []
    for n in range(1, 3*m + 2):
        plus = prod(2*m*n + k for k in range(1, 2*m + 1))
        minus = prod(2*m*n - k for k in range(1, 2*m + 1))
        
        P_pos = sum(vars[i] * n**i for i in range(2*m + 1))
        P_neg = sum(vars[i] * (-n)**i for i in range(2*m + 1))
        
        sign_m = (-1)**m
        Q_val = sum(vars[2*m + 1 + i] * (n**2)**i for i in range(2*m)) + (n**2)**(2*m)
        
        eq = plus * P_pos * b[n+1] + sign_m * minus * P_neg * b[n-1] - Q_val * b[n]
        eqs.append(eq)
        
    for k in range(1, m + 1):
        eq = sum(vars[i] * k**i for i in range(2*m + 1)) - sum(vars[i] * (1 - k)**i for i in range(2*m + 1))
        eqs.append(eq)
        
    A = matrix(QQ, n_vars, n_vars)
    B = vector(QQ, n_vars)
    
    for r_idx, eq in enumerate(eqs):
        for c_idx, v in enumerate(vars):
            A[r_idx, c_idx] = eq.coefficient(v)
        B[r_idx] = -eq.subs({v: 0 for v in vars})
        
    sol = A.solve_right(B)
    d_sol = [sol[2*m + 1 + i] for i in range(2*m)] + [1]
    
    R_y = ComplexField(1000)['y']
    Q_poly = sum(ComplexField(1000)(d_sol[i]) * R_y.gen()**i for i in range(2*m + 1))
    
    roots = Q_poly.roots()
    
    all_real_in_01 = True
    for r, mult in roots:
        is_real = abs(r.imag()) < 1e-50
        in_01 = r.real() >= 0 and r.real() <= 1
        if not is_real or not in_01:
            all_real_in_01 = False
            print(f"m = {m}: Root violation: root = {r}")
            break
            
    if all_real_in_01:
        print(f"m = {m}: ALL roots are real and in [0, 1]")
    else:
        print(f"m = {m}: ROOT VIOLATED!")
