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

for m in range(1, 30):
    # We set up the linear system for c0..c2m and d0..d2m (total 4m+2 variables)
    # We use 3m recurrence equations and m symmetry equations, total 4m equations.
    # Wait, we need 4m+2 variables, so we need 4m+2 equations.
    # Let's use 3m+2 recurrence equations and m symmetry equations, total 4m+2 equations.
    # Setting d2m = 1, so we have 4m+1 variables and 4m+2 equations?
    # No, let's just set d2m = 1, then we have c0..c2m (2m+1 variables) and d0..d2m-1 (2m variables), total 4m+1 variables.
    # We can write 3m+1 recurrence equations (n = 1..3m+1) and m symmetry equations (k = 1..m).
    # Total equations: (3m+1) + m = 4m+1 equations!
    # This is a square linear system!
    
    n_vars = 4 * m + 1
    A_mat = np.zeros((n_vars, n_vars))
    B_vec = np.zeros(n_vars)
    
    # Recurrence equations: n = 1 .. 3m+1
    # plus * P_pos * b(n+1) + (-1)^m * minus * P_neg * b(n-1) - Q_val * b(n) = 0
    # With d2m = 1, the term Q_val has d2m * n^(4m) * b(n), which we move to RHS.
    b = [a(m*i) for i in range(3*m + 3)]
    
    row = 0
    for n in range(1, 3*m + 2):
        plus = 1.0
        for k in range(1, 2*m + 1):
            plus *= (2*m*n + k)
        minus = 1.0
        for k in range(1, 2*m + 1):
            minus *= (2*m*n - k)
            
        # P_pos terms: sum_{i=0}^{2m} c_i * n^i * plus * b(n+1)
        for i in range(2*m + 1):
            A_mat[row, i] = (n**i) * plus * b[n+1]
            
        # P_neg terms: sum_{i=0}^{2m} c_i * (-n)^i * (-1)^m * minus * b(n-1)
        sign = (-1.0)**m
        for i in range(2*m + 1):
            A_mat[row, i] += ((-n)**i) * sign * minus * b[n-1]
            
        # Q_val terms: - sum_{i=0}^{2m-1} d_i * (n^2)^i * b(n)
        for i in range(2*m):
            A_mat[row, 2*m + 1 + i] = - (n**(2*i)) * b[n]
            
        # RHS term for d2m = 1: d2m * (n^2)^2m * b(n) = n^(4m) * b(n)
        B_vec[row] = (n**(4*m)) * b[n]
        row += 1
        
    # Symmetry equations: k = 1 .. m
    # P(k) - P(1-k) = 0
    for k in range(1, m + 1):
        for i in range(2*m + 1):
            A_mat[row, i] = (k**i) - ((1 - k)**i)
        row += 1
        
    # Solve the system
    try:
        sol = np.linalg.solve(A_mat, B_vec)
        c_vals = list(sol[:2*m+1])
        d_vals = list(sol[2*m+1:]) + [1.0]
        
        P_roots = np.roots(c_vals[::-1])
        Q_roots = np.roots(d_vals[::-1])
        
        P_ok = True
        for r in P_roots:
            if abs(r.imag) > 1e-4 or r.real < -1e-4 or r.real > 1 + 1e-4:
                P_ok = False
                break
                
        Q_ok = True
        for r in Q_roots:
            if abs(r.imag) > 1e-4 or r.real < -1e-4 or r.real > 1 + 1e-4:
                Q_ok = False
                break
                
        print(f"m = {m}: P roots OK: {P_ok}, Q roots OK: {Q_ok}")
        if not P_ok or not Q_ok:
            print(f"  P roots: {P_roots}")
            print(f"  Q roots: {Q_roots}")
            break
    except np.linalg.LinAlgError:
        print(f"m = {m}: Singular matrix")
