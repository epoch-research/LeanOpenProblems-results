import sympy as sp
import numpy as np

def is_prime(n):
    if n < 2: return False
    if n in (2, 3): return True
    if n % 2 == 0 or n % 3 == 0: return False
    for i in range(5, int(n**0.5) + 1, 6):
        if n % i == 0 or n % (i+2) == 0: return False
    return True

for n in [29, 31, 33, 35]:
    M = np.zeros((n, n), dtype=int)
    for i in range(n):
        for j in range(n):
            if is_prime((i+1)**2 + (j+1)**2):
                M[i,j] = 1
    det = int(round(np.linalg.det(M)))
    
    k = n // 2
    B = np.zeros((k, k), dtype=int)
    for x in range(k):
        for y in range(k):
            if is_prime((2*x+2)**2 + (2*y+3)**2):
                B[x,y] = 1
    detB = int(round(np.linalg.det(B)))
    
    print(f"n={n}, det={det}, detB={detB}, detB^2 = {detB**2}")

