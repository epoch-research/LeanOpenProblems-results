import sympy as sp
import numpy as np

def is_prime(n):
    if n < 2: return False
    if n in (2, 3): return True
    if n % 2 == 0 or n % 3 == 0: return False
    for i in range(5, int(n**0.5) + 1, 6):
        if n % i == 0 or n % (i+2) == 0: return False
    return True

M = sp.zeros(29, 29)
for i in range(29):
    for j in range(29):
        if is_prime((i+1)**2 + (j+1)**2):
            M[i, j] = 1

print(M.det())
