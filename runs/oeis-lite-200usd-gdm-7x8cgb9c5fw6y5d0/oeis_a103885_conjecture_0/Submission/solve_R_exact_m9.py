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

for m in [9]:
    print(f"\nSolving exactly for m = {m}...")
    num_unknowns = 3 * m + 1
    A_mat = sp.Matrix.zeros(num_unknowns, num_unknowns)
    B_vec = sp.Matrix.zeros(num_unknowns, 1)

    a_vals = [sp.Rational(a(m * i)) for i in range(3 * m + 5)]

    for idx_n, n in enumerate(range(1, 3 * m + 2)):
        plus = sp.Rational(math.prod(2*m*n + k for k in range(1, 2*m + 1)))
        minus = sp.Rational(math.prod(2*m*n - k for k in range(1, 2*m + 1)))
        
        for j in range(m + 1):
            val_p = sp.Rational((n * (1 - n))**j)
            val_m = sp.Rational((-n * (1 + n))**j)
            coeff_e = plus * val_p * a_vals[n+1] + sp.Rational((-1)**m) * minus * val_m * a_vals[n-1]
            A_mat[idx_n, j] = coeff_e
            
        for i in range(2 * m):
            coeff_d = - sp.Rational(n**(2*i)) * a_vals[n]
            A_mat[idx_n, m + 1 + i] = coeff_d
            
        coeff_d_2m = - sp.Rational(n**(2*(2*m))) * a_vals[n]
        B_vec[idx_n, 0] = - coeff_d_2m
        
    sol = A_mat.LUsolve(B_vec)
    e_vals = [sol[j, 0] for j in range(m + 1)]
    d_vals = [sol[m + 1 + i, 0] for i in range(2 * m)] + [1]

    y = sp.Symbol('y')
    R_poly = sum(e_vals[i] * y**i for i in range(m+1))
    Q_poly = sum(d_vals[i] * y**i for i in range(2*m+1))

    print("R_poly real roots count:", len(sp.real_roots(R_poly)))
    print("Q_poly real roots count:", len(sp.real_roots(Q_poly)))
