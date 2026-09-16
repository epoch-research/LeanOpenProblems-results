import numpy as np

def is_prime(n):
    if n < 2: return False
    if n in (2, 3): return True
    if n % 2 == 0 or n % 3 == 0: return False
    for i in range(5, int(n**0.5) + 1, 6):
        if n % i == 0 or n % (i+2) == 0: return False
    return True

for n in range(6, 100):
    M = np.zeros((n, n), dtype=int)
    for i in range(n):
        for j in range(n):
            if is_prime((i+1)**2 + (j+1)**2):
                M[i,j] = 1
    
    # Check for identical rows
    for i in range(n):
        for k in range(i+1, n):
            if np.array_equal(M[i], M[k]):
                print(f"n={n}: Row {i} (x={i+1}) and Row {k} (x={k+1}) are identical")

