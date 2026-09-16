import numpy as np

def is_prime(n):
    if n < 2: return False
    if n in (2, 3): return True
    if n % 2 == 0 or n % 3 == 0: return False
    for i in range(5, int(n**0.5) + 1, 6):
        if n % i == 0 or n % (i+2) == 0: return False
    return True

k = 14
A = np.zeros((k, k), dtype=int)
for x in range(k):
    for y in range(k):
        if is_prime((2*x+2)**2 + (2*y+3)**2):
            A[x, y] = 1

print("det(A) for n=29:", np.linalg.det(A))

