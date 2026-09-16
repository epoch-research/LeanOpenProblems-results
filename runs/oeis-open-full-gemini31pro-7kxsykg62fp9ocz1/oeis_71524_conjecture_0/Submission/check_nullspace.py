import sympy as sp

def is_prime(n):
    if n < 2: return False
    if n in (2, 3): return True
    if n % 2 == 0 or n % 3 == 0: return False
    for i in range(5, int(n**0.5) + 1, 6):
        if n % i == 0 or n % (i+2) == 0: return False
    return True

for n in [6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 28]:
    M = sp.zeros(n, n)
    for i in range(n):
        for j in range(n):
            if is_prime((i+1)**2 + (j+1)**2):
                M[i, j] = 1
    
    null = M.nullspace()
    print(f"n={n}, nullspace dim={len(null)}")
    if len(null) > 0:
        v = null[0]
        # find non-zero indices
        indices = [j+1 for j in range(n) if v[j] != 0]
        print(f"  Involved columns: {indices}")
        print(f"  Vector: {v.T}")
