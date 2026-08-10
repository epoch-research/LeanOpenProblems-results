import math
import mpmath as mp

# Set precision to 1000 digits
mp.mp.dps = 1000

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
    print(f"\n--- Checking m = {m} ---")
    n_vars = 4 * m + 1
    A_mat = mp.matrix(n_vars, n_vars)
    B_vec = mp.matrix(n_vars, 1)
    
    b = [mp.mpf(a(m*i)) for i in range(3*m + 3)]
    
    row = 0
    for n in range(1, 3*m + 2):
        plus = mp.mpf(1)
        for k in range(1, 2*m + 1):
            plus *= (2*m*n + k)
        minus = mp.mpf(1)
        for k in range(1, 2*m + 1):
            minus *= (2*m*n - k)
            
        for i in range(2*m + 1):
            A_mat[row, i] = (mp.mpf(n)**i) * plus * b[n+1]
            
        sign = mp.mpf((-1)**m)
        for i in range(2*m + 1):
            A_mat[row, i] += (mp.mpf(-n)**i) * sign * minus * b[n-1]
            
        for i in range(2*m):
            A_mat[row, 2*m + 1 + i] = - (mp.mpf(n)**(2*i)) * b[n]
            
        B_vec[row, 0] = (mp.mpf(n)**(4*m)) * b[n]
        row += 1
        
    for k in range(1, m + 1):
        for i in range(2*m + 1):
            A_mat[row, i] = (mp.mpf(k)**i) - (mp.mpf(1 - k)**i)
        row += 1
        
    try:
        sol = mp.lu_solve(A_mat, B_vec)
        c_vals = [sol[i, 0] for i in range(2*m+1)]
        d_vals = [sol[2*m+1+i, 0] for i in range(2*m)] + [mp.mpf(1)]
        
        # Check roots of P and Q
        P_roots = mp.polyroots(c_vals[::-1], maxsteps=200)
        Q_roots = mp.polyroots(d_vals[::-1], maxsteps=200)
        
        P_ok = True
        for r in P_roots:
            if abs(r.imag) > 1e-15 or r.real < 0 or r.real > 1:
                P_ok = False
                print(f"  P Root violated: {r}")
                
        Q_ok = True
        for r in Q_roots:
            if abs(r.imag) > 1e-15 or r.real < 0 or r.real > 1:
                Q_ok = False
                print(f"  Q Root violated: {r}")
                
        print(f"  m = {m}: P roots OK: {P_ok}, Q roots OK: {Q_ok}")
    except Exception as e:
        print(f"  m = {m}: Error {e}")
