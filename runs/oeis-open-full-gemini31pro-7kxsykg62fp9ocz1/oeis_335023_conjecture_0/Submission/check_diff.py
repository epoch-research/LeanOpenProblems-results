P = 1093**2

def dc_mod(a, b):
    if a + 1 == b:
        k = a + 1
        return (k % P, 1 if k % 2 == 0 else P - 1)
    mid = (a + b) // 2
    x1, z1 = dc_mod(a, mid)
    x2, z2 = dc_mod(mid, b)
    return ((x2 * x1) % P, (x2 * z1 + z2 * x1) % P)

print(dc_mod(0, 4))
