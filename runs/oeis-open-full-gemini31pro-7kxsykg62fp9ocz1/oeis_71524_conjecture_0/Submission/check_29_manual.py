import sympy as sp

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(n**0.5) + 1):
        if n % i == 0: return False
    return True

M = sp.zeros(29, 29)
for i in range(29):
    for j in range(29):
        if is_prime((i+1)**2 + (j+1)**2):
            M[i, j] = 1

print("det(M_29) =", M.det())
