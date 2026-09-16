import numpy as np
import sympy as sp

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(n**0.5) + 1):
        if n % i == 0: return False
    return True

m = 14
B = np.zeros((m, m), dtype=int)
for i in range(m):
    for j in range(m):
        if is_prime((2*i+1)**2 + (2*(j+1))**2):
            B[i,j] = 1

M = sp.Matrix(B)
nullspace = M.nullspace()
print("Nullspace for n=28:", nullspace)

