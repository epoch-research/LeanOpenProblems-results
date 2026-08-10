import mpmath as mp
import math

mp.mp.dps = 100

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

for m in range(1, 15):
    num_unknowns = 3 * m + 1
    A_mat = mp.matrix(num_unknowns, num_unknowns)
    B_vec = mp.matrix(num_unknowns, 1)
    
    a_vals = [mp.mpf(a(m * i)) for i in range(3 * m + 5)]
    
    for idx_n, n in enumerate(range(1, 3 * m + 2)):
        plus = mp.mpf(1)
        for k in range(1, 2*m + 1):
            plus *= (2*m*n + k)
            
        minus = mp.mpf(1)
        for k in range(1, 2*m + 1):
            minus *= (2*m*n - k)
            
        for j in range(m + 1):
            val_p = mp.mpf(n * (1 - n))**j
            val_m = mp.mpf(-n * (1 + n))**j
            coeff_e = plus * val_p * a_vals[n+1] + ((-1)**m) * minus * val_m * a_vals[n-1]
            A_mat[idx_n, j] = coeff_e
            
        for i in range(2 * m):
            coeff_d = - mp.mpf(n**(2*i)) * a_vals[n]
            A_mat[idx_n, m + 1 + i] = coeff_d
            
        coeff_d_2m = - mp.mpf(n**(2*(2*m))) * a_vals[n]
        B_vec[idx_n, 0] = - coeff_d_2m
        
    try:
        sol = mp.lu_solve(A_mat, B_vec)
        e_vals = [sol[j, 0] for j in range(m + 1)]
        d_vals = [sol[m + 1 + i, 0] for i in range(2 * m)] + [mp.mpf(1)]
        
        roots_R = mp.polyroots(e_vals[::-1])
        all_real_R = all(abs(r.imag) < 1e-15 for r in roots_R)
        all_lt_quarter = all(r.real < 0.25 for r in roots_R)
        
        roots_Q = mp.polyroots(d_vals[::-1])
        all_real_Q = all(abs(r.imag) < 1e-15 for r in roots_Q)
        all_in_01 = all(0 <= r.real <= 1 for r in roots_Q)
        
        print(f"m = {m:2d}: R real: {all_real_R}, R < 0.25: {all_lt_quarter} | Q real: {all_real_Q}, Q in [0,1]: {all_in_01}")
    except Exception as e:
        print(f"m = {m:2d}: Failed with error: {e}")
