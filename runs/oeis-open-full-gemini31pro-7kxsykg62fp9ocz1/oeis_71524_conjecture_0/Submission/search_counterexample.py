import numpy as np
import sympy as sp
import sys

sys.set_int_max_str_digits(1000000)

def is_prime(n):
    if n < 2: return False
    if n in (2, 3): return True
    if n % 2 == 0 or n % 3 == 0: return False
    for i in range(5, int(n**0.5) + 1, 6):
        if n % i == 0 or n % (i+2) == 0: return False
    return True

def check_n(n):
    # build matrix
    k = n // 2
    if n % 2 == 0:
        # check B: size k x k, B_{x,y} = is_prime((2x+1)^2 + (2y+2)^2) for x,y in 0..k-1
        M = np.zeros((k, k), dtype=int)
        for x in range(k):
            for y in range(k):
                if is_prime((2*x+1)**2 + (2*y+2)**2):
                    M[x, y] = 1
    else:
        # check A: size k x k, A_{x,y} = is_prime((2x+2)^2 + (2y+3)^2) for x,y in 0..k-1
        M = np.zeros((k, k), dtype=int)
        for x in range(k):
            for y in range(k):
                if is_prime((2*x+2)**2 + (2*y+3)**2):
                    M[x, y] = 1
    
    # check if rank is deficient
    # First fast check over a few primes
    for p in [1000000007, 1000000009]:
        Mp = M % p
        # just use sympy det modulo
        if sp.Matrix(M).det() == 0:
            return True
        else:
            return False

for n in range(29, 300):
    if check_n(n):
        print(f"COUNTEREXAMPLE FOUND: n={n}")
        break
    if n % 10 == 0:
        print(f"Checked n={n}")

