import numpy as np

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(n**0.5) + 1):
        if n % i == 0: return False
    return True

for n in range(6, 29):
    m = n // 2
    B = np.zeros((m, m), dtype=int)
    for i in range(m):
        for j in range(m):
            if is_prime((2*i+1)**2 + (2*(j+1))**2):
                B[i,j] = 1
    # Check for identical rows
    has_identical = False
    for i in range(m):
        for k in range(i+1, m):
            if np.array_equal(B[i], B[k]):
                has_identical = True
                print(f"n={n}: Row {i} (x={2*i+1}) and Row {k} (x={2*k+1}) are identical: {B[i]}")
    if not has_identical:
        print(f"n={n}: No identical rows, but det is {np.linalg.det(B):.0f}")

