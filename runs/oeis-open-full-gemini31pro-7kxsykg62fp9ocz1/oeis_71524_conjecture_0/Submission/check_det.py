import sympy as sp
import numpy as np

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(n**0.5) + 1):
        if n % i == 0: return False
    return True

def get_matrix(n):
    M = np.zeros((n, n), dtype=int)
    for i in range(n):
        for j in range(n):
            if is_prime((i+1)**2 + (j+1)**2):
                M[i,j] = 1
    return M

for n in range(29, 50):
    det = sp.Matrix(get_matrix(n)).det()
    factors = sp.factorint(det)
    print(f"n={n}, det={det}, factors={factors}")

