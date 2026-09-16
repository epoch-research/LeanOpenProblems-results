import numpy as np
import sympy as sp

def is_prime(n):
    if n < 2: return False
    if n in (2, 3): return True
    if n % 2 == 0 or n % 3 == 0: return False
    for i in range(5, int(n**0.5) + 1, 6):
        if n % i == 0 or n % (i+2) == 0: return False
    return True

for n in [28, 29, 30]:
    k = n // 2
    if n % 2 == 0:
        M = np.zeros((k, k), dtype=int)
        for x in range(k):
            for y in range(k):
                if is_prime((2*x+1)**2 + (2*y+2)**2):
                    M[x, y] = 1
    else:
        M = np.zeros((k, k), dtype=int)
        for x in range(k):
            for y in range(k):
                if is_prime((2*x+2)**2 + (2*y+3)**2):
                    M[x, y] = 1
    
    det = sp.Matrix(M).det()
    print(f"n={n}, det={det}")

