import numpy as np

def is_prime(n):
    if n < 2: return False
    if n in (2, 3): return True
    if n % 2 == 0 or n % 3 == 0: return False
    for i in range(5, int(n**0.5) + 1, 6):
        if n % i == 0 or n % (i+2) == 0: return False
    return True

def rank_gf2(M):
    M = np.copy(M) % 2
    rows, cols = M.shape
    r = 0
    for c in range(cols):
        pivot = r
        while pivot < rows and M[pivot, c] == 0:
            pivot += 1
        if pivot == rows:
            continue
        M[[r, pivot]] = M[[pivot, r]]
        for i in range(r + 1, rows):
            if M[i, c] != 0:
                M[i] = (M[i] + M[r]) % 2
        r += 1
    return r

for n in range(29, 200):
    k = n // 2
    M = np.zeros((k, k), dtype=int)
    if n % 2 == 0:
        for x in range(k):
            for y in range(k):
                if is_prime((2*x+1)**2 + (2*y+2)**2):
                    M[x, y] = 1
    else:
        for x in range(k):
            for y in range(k):
                if is_prime((2*x+2)**2 + (2*y+3)**2):
                    M[x, y] = 1
    
    r = rank_gf2(M)
    if r < k:
        print(f"n={n} is singular over GF(2)! rank={r}, k={k}")

