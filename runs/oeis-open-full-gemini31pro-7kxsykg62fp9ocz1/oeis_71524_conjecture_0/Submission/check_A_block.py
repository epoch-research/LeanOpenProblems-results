import numpy as np

def is_prime(n):
    if n < 2: return False
    if n in (2, 3): return True
    if n % 2 == 0 or n % 3 == 0: return False
    for i in range(5, int(n**0.5) + 1, 6):
        if n % i == 0 or n % (i+2) == 0: return False
    return True

for n in range(5, 10):
    k_odd = (n + 1) // 2
    A = np.zeros((k_odd, k_odd), dtype=int)
    for x in range(k_odd):
        for y in range(k_odd):
            if is_prime((2*x+1)**2 + (2*y+1)**2):
                A[x,y] = 1
    print(f"n={n}, A=\n{A}")
