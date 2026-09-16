P = 1093**2

def dc_mod(a, b):
    if a + 1 == b:
        k = a + 1
        # F_k = k * F_{k-1} + (-1)^k (k-1)!
        # (fact_k, F_k) = (k * fact_{k-1}, k * F_{k-1} + (-1)^k fact_{k-1})
        # So X = k, Z = (-1)^k
        return (k % P, 1 if k % 2 == 0 else P - 1)
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
        sign = 1 if k % 2 == 0 else P - 1
        F = (k * F + sign * fact) % P
        fact = (fact * k) % P
    return fact, F

x, z = dc_mod(0, 100)
x2, z2 = exact(100)
print(x == x2, z == z2)
