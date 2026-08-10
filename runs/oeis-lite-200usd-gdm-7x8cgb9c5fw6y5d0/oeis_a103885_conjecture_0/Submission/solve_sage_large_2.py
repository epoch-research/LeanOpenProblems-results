from sage.all import *
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
    print(f"\n--- m = {m} ---")
    num_unknowns = 3 * m + 1
    A_mat = matrix(QQ, num_unknowns, num_unknowns)
    B_vec = matrix(QQ, num_unknowns, 1)

    a_vals = [QQ(a(m * i)) for i in range(3 * m + 5)]

    for idx_n, n in enumerate(range(1, 3 * m + 2)):
        plus = QQ(math.prod(2*m*n + k for k in range(1, 2*m + 1)))
        minus = QQ(math.prod(2*m*n - k for k in range(1, 2*m + 1)))
        
        for j in range(m + 1):
            val_p = QQ((n * (1 - n))**j)
            val_m = QQ((-n * (1 + n))**j)
            coeff_e = plus * val_p * a_vals[n+1] + QQ((-1)**m) * minus * val_m * a_vals[n-1]
            A_mat[idx_n, j] = coeff_e
            
        for i in range(2 * m):
            coeff_d = - QQ(n**(2*i)) * a_vals[n]
            A_mat[idx_n, m + 1 + i] = coeff_d
            
        coeff_d_2m = - QQ(n**(2*(2*m))) * a_vals[n]
        B_vec[idx_n, 0] = - coeff_d_2m
        
    try:
        sol = A_mat.solve_right(B_vec)
        e_vals = [sol[j, 0] for j in range(m + 1)]
        d_vals = [sol[m + 1 + i, 0] for i in range(2 * m)] + [QQ(1)]
        
        y = SR.var('y')
        P_poly = sum(QQ(e_vals[i]) * (y * (1 - y))**i for i in range(m + 1))
        Q_poly = sum(QQ(d_vals[i]) * y**i for i in range(2*m+1))
        
        P_roots = P_poly.roots(ring=CC)
        all_P_ok = True
        for root, mult in P_roots:
            if abs(root.imag()) > 1e-12 or root.real() < 0 or root.real() > 1:
                all_P_ok = False
                print("Violation P root:", root)
        print("All P OK:", all_P_ok)
        
        Q_roots = Q_poly.roots(ring=CC)
        all_Q_ok = True
        for root, mult in Q_roots:
            if abs(root.imag()) > 1e-12 or root.real() < 0 or root.real() > 1:
                all_Q_ok = False
                print("Violation Q root:", root)
        print("All Q OK:", all_Q_ok)
        
    except Exception as e:
        print("Error:", e)
