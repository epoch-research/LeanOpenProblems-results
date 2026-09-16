import sympy as sp
import numpy as np

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(n**0.5) + 1):
        if n % i == 0: return False
    return True

def get_B(m):
    B = np.zeros((m, m), dtype=int)
    for i in range(m):
        for j in range(m):
            if is_prime((2*i+1)**2 + (2*(j+1))**2):
                B[i,j] = 1
    return B

for m in range(60, 150):
    B = sp.Matrix(get_B(m))
    detB = B.det()
    n = 2*m
    if detB == 0:
        print(f"FOUND ZERO! n={n}, n-1={n-1}")
        break
    if m % 10 == 0:
        print(f"Checked up to n={n}, det={detB}")

