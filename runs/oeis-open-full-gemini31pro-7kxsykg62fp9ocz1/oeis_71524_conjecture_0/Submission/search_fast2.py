import numpy as np
import sys

def is_prime(n):
    if n < 2: return False
    if n in (2, 3): return True
    if n % 2 == 0 or n % 3 == 0: return False
    for i in range(5, int(n**0.5) + 1, 6):
        if n % i == 0 or n % (i+2) == 0: return False
    return True

def rank_mod_p(M, p):
    M = np.copy(M) % p
    rows, cols = M.shape
    r = 0
    for c in range(cols):
        pivot = r
        while pivot < rows and M[pivot, c] == 0:
            pivot += 1
        if pivot == rows:
            continue
        M[[r, pivot]] = M[[pivot, r]]
        inv = pow(int(M[r, c]), p - 2, p)
        for i in range(r + 1, rows):
            if M[i, c] != 0:
                factor = (M[i, c] * inv) % p
                M[i] = (M[i] - factor * M[r]) % p
        r += 1
    return r

p = 1000000007

for n in range(600, 2000):
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
    
    r = rank_mod_p(M, p)
    if r < k:
        print(f"POSSIBLE COUNTEREXAMPLE: n={n}, rank={r}, k={k}")
        if rank_mod_p(M, 1000000009) < k:
            print(f"CONFIRMED ZERO DET MOD 2 PRIMES FOR n={n}")
            sys.exit(0)
    
    if n % 100 == 0:
        print(f"Checked n={n}")

