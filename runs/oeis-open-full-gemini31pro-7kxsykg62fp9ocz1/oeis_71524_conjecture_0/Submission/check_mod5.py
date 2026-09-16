import numpy as np

def is_prime(n):
    if n < 2: return False
    if n in (2, 3): return True
    if n % 2 == 0 or n % 3 == 0: return False
    for i in range(5, int(n**0.5) + 1, 6):
        if n % i == 0 or n % (i+2) == 0: return False
    return True

for n in range(29, 40):
    k = n // 2
    M = np.zeros((k, k), dtype=int)
    for x in range(k):
        for y in range(k):
            if is_prime((2*x+1)**2 + (2*y+2)**2):
                M[x, y] = 1
    
    M = M % 5
    print(f"n={n}, det mod 5 = {int(round(np.linalg.det(M))) % 5}")
