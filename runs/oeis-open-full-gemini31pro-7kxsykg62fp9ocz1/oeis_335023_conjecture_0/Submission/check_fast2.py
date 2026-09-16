P = 1093**1092

def dc_mod(a, b):
    if a + 1 == b:
        k = a + 1
        return (k % P, k % P if k % 2 == 0 else (P - k % P) % P)
    mid = (a + b) // 2
    x1, z1 = dc_mod(a, mid)
    x2, z2 = dc_mod(mid, b)
    x = (x2 * x1) % P
    z = (x2 * z1 + z2 * x1) % P
    return (x, z)

def exact(M):
    F = 0
    fact = 1
    for k in range(1, M+1):
        sign = 1 if k % 2 == 0 else -1
        F = (k * F + sign * fact * k) % P
        fact = (fact * k) % P
    return fact, F

x, z = dc_mod(0, 1000)
x2, z2 = exact(1000)
print(x == x2, z == z2)
