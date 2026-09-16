def dc(a, b):
    if a + 1 == b:
        k = a + 1
        return (k, 1 if k % 2 == 0 else -1)
    mid = (a + b) // 2
    x1, z1 = dc(a, mid)
    x2, z2 = dc(mid, b)
    x = x2 * x1
    z = x2 * z1 + z2 * x1
    return (x, z)

import time
start = time.time()
x, z = dc(0, 1194648)
print("Time:", time.time() - start)
print(len(str(z)))
