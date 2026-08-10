import numpy as np
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

for m in range(1, 9):
    print(f"\n--- m = {m} ---")
    n_vars = 3 * m + 1
    A_mat = np.zeros((n_vars, n_vars))
    B_vec = np.zeros(n_vars)
    
    # Precompute b
    b = [float(a(m*i)) for i in range(3*m + 3)]
    
    for idx_n, n in enumerate(range(1, 3 * m + 2)):
        plus = 1.0
        for k in range(1, 2*m + 1):
            plus *= (2*m*n + k)
        minus = 1.0
        for k in range(1, 2*m + 1):
            minus *= (2*m*n - k)
            
        for j in range(m + 1):
            val_p = (n * (1.0 - n))**j
            val_m = (-n * (1.0 + n))**j
            coeff_e = plus * val_p * b[idx_n+2] + ((-1)**m) * minus * val_m * b[idx_n]
            A_mat[idx_n, j] = coeff_e
            
        for i in range(2 * m):
            coeff_d = - (n**(2*i)) * b[idx_n+1]
            A_mat[idx_n, m + 1 + i] = coeff_d
            
        coeff_d_2m = - (n**(2*(2*m))) * b[idx_n+1]
        B_vec[idx_n] = - coeff_d_2m
        
    # Scale the columns of A_mat
    col_norms = np.linalg.norm(A_mat, axis=0)
    for j in range(n_vars):
        if col_norms[j] > 0:
            A_mat[:, j] /= col_norms[j]
            
    try:
        sol_scaled = np.linalg.solve(A_mat, B_vec)
        sol = sol_scaled / col_norms
        
        e_vals = sol[:m+1]
        d_vals = list(sol[m+1:]) + [1.0]
        
        roots_R = np.roots(e_vals[::-1])
        roots_Q = np.roots(d_vals[::-1])
        
        print("  R roots (real parts):", [r.real for r in roots_R])
        print("  R roots (imag parts):", [r.imag for r in roots_R])
        print("  Q roots (real parts):", [r.real for r in roots_Q])
        print("  Q roots (imag parts):", [r.imag for r in roots_Q])
    except Exception as e:
        print(f"  Error: {e}")
