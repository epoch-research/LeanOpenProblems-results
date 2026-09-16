def dc(a, b):
    if a + 1 == b:
        k = a + 1
        return (k, 1 if k % 2 == 0 else -1)
    mid = (a + b) // 2
    x1, z1 = dc(a, mid)
    x2, z2 = dc(mid, b)
    return (x2 * x1, x2 * z1 + z2 * x1)

import math

def F_aux(n):
    if n < 2: return 0
    ans = 0
    fact = math.factorial(n)
    for k in range(2, n+1):
        ans += (fact // k) * (1 if k % 2 == 0 else -1)
    return ans

x, z = dc(0, 10)
print("dc F_10 full:", z)
print("F_aux(10):", F_aux(10))
print("z + x:", z + x)
