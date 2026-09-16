import numpy as np

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(n**0.5) + 1):
        if n % i == 0: return False
    return True

m = 20
B = np.zeros((m, m), dtype=int)
for i in range(m):
    for j in range(m):
        if is_prime((2*i+1)**2 + (2*(j+1))**2):
            B[i,j] = 1

print("Row sums:", B.sum(axis=1))
print("Col sums:", B.sum(axis=0))
