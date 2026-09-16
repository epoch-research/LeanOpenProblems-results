import numpy as np

def is_prime(n):
    if n < 2: return False
    if n in (2, 3): return True
    if n % 2 == 0 or n % 3 == 0: return False
    for i in range(5, int(n**0.5) + 1, 6):
        if n % i == 0 or n % (i+2) == 0: return False
    return True

for n in [30, 40, 50]:
    k = n // 2
    B = np.zeros((k, k), dtype=int)
    for x in range(k):
        for y in range(k):
            if is_prime((2*x+1)**2 + (2*y+2)**2):
                B[x,y] = 1
    
    print(f"n={n}")
    for i in range(k):
        row_sum = sum(B[i])
        diag = B[i,i]
        # strictly diagonally dominant if |B_{i,i}| > sum_{j != i} |B_{i,j}|
        if diag <= row_sum - diag:
            print(f"  Row {i} is NOT strictly diagonally dominant (diag={diag}, sum={row_sum})")
