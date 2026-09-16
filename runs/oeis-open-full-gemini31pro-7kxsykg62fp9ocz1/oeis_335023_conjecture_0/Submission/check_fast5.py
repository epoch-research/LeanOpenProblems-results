P = 1093**1093

def dc_mod(a, b):
    if a + 1 == b:
        k = a + 1
        return (k % P, 1 if k % 2 == 0 else P - 1)
    mid = (a + b) // 2
    x1, z1 = dc_mod(a, mid)
    x2, z2 = dc_mod(mid, b)
    x = (x2 * x1) % P
    z = (x2 * z1 + z2 * x1) % P
    return (x, z)

x, z = dc_mod(0, 1194648)
print("x % P == 0:", x == 0)
print("z % P == 0:", z == 0)
print("x % 1093**1092 == 0:", x % (1093**1092) == 0)
print("z % 1093**1092 == 0:", z % (1093**1092) == 0)
