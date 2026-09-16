import sympy as sp

def is_prime(n):
    if n < 2: return False
    if n in (2, 3): return True
    if n % 2 == 0 or n % 3 == 0: return False
    for i in range(5, int(n**0.5) + 1, 6):
        if n % i == 0 or n % (i+2) == 0: return False
    return True

n = 29
M = sp.zeros(n, n)
for i in range(n):
    for j in range(n):
        if is_prime((i+1)**2 + (j+1)**2):
            M[i, j] = 1

print(f"SymPy EXACT det for n=29: {M.det()}")
