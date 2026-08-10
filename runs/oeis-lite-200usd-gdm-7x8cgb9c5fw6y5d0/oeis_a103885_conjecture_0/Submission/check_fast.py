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

for m in range(1, 16):
    # Set up the linear system for the coefficients of P and Q
    # P has degree 2m: P(x) = c0 + c1 x + ... + c_{2m} x^{2m}
    # Q has degree 2m: Q(x) = d0 + d1 x + ... + d_{2m} x^{2m}
    # Using symmetry: P(x) = P(1-x), which means we can write P(x) = sum_{j=0}^m e_j (x(1-x))^j
    # So P has m+1 coefficients e_0, ..., e_m.
    # Q has 2m+1 coefficients d_0, ..., d_{2m}.
    # Total number of unknowns: (m+1) + (2m+1) = 3m + 2.
    # We can scale the system by setting d_{2m} = 1.
    # This leaves 3m + 1 unknowns: e_0, ..., e_m, d_0, ..., d_{2m-1}.
    # We can generate 3m + 1 equations by evaluating the recurrence for n = 1, ..., 3m + 1.
    
    num_unknowns = 3 * m + 1
    A_mat = np.zeros((num_unknowns, num_unknowns))
    B_vec = np.zeros(num_unknowns)
    
    # Precompute a_vals for speed
    a_vals = [a(m * i) for i in range(3 * m + 5)]
    
    for idx_n, n in enumerate(range(1, 3 * m + 2)):
        # prod_factor_plus m n
        plus = 1.0
        for k in range(1, 2*m + 1):
            plus *= (2*m*n + k)
            
        # prod_factor_minus m n
        minus = 1.0
        for k in range(1, 2*m + 1):
            minus *= (2*m*n - k)
            
        # Recurrence:
        # plus * P(n) * a(m*(n+1)) + (-1)^m * minus * P(-n) * a(m*(n-1)) - Q(n^2) * a(m*n) = 0
        # Let's write P(x) = sum_{j=0}^m e_j (x(1-x))^j
        # So P(n) coefficient of e_j is (n(1-n))^j
        # P(-n) coefficient of e_j is (-n(1+n))^j
        # Q(n^2) coefficient of d_i is (n^2)^i = n^{2i}
        
        # Column 0..m: e_j
        for j in range(m + 1):
            val_p = (n * (1.0 - n))**j
            val_m = (-n * (1.0 + n))**j
            coeff_e = plus * val_p * a_vals[n+1] + ((-1)**m) * minus * val_m * a_vals[n-1]
            A_mat[idx_n, j] = coeff_e
            
        # Column m+1..3m: d_i for i = 0..2m-1
        for i in range(2 * m):
            coeff_d = - (n**(2*i)) * a_vals[n]
            A_mat[idx_n, m + 1 + i] = coeff_d
            
        # Constant term from d_{2m} = 1
        coeff_d_2m = - (n**(2*(2*m))) * a_vals[n]
        B_vec[idx_n] = - coeff_d_2m
        
    # Solve the system
    try:
        sol = np.linalg.solve(A_mat, B_vec)
        e_vals = sol[:m+1]
        d_vals = list(sol[m+1:]) + [1.0]
        
        # Check roots of R(y)
        roots_R = np.roots(e_vals[::-1])
        all_real_R = np.all(np.abs(np.imag(roots_R)) < 1e-5)
        all_lt_quarter = np.all(np.real(roots_R) < 0.25)
        
        # Check roots of Q(w)
        roots_Q = np.roots(d_vals[::-1])
        all_real_Q = np.all(np.abs(np.imag(roots_Q)) < 1e-5)
        all_in_01 = np.all((np.real(roots_Q) >= 0) & (np.real(roots_Q) <= 1))
        
        print(f"m = {m:2d}: R real: {all_real_R}, R < 0.25: {all_lt_quarter} | Q real: {all_real_Q}, Q in [0,1]: {all_in_01}")
    except np.linalg.LinAlgError:
        print(f"m = {m:2d}: Linear solve failed!")
