def lcm(a, b):
    import math
    return abs(a*b) // math.gcd(a, b)

x = [0, 1]
for n in range(2, 20000):
    val = 2 * x[-1] + lcm(x[-1], n)
    x.append(val)

import math
g = [1]
q = 23
for i in range(1, 4):
    idx = g[-1] * (q - 2) - 1
    val = math.gcd(x[idx], g[-1] * (q - 2))
    g.append(val)
    print(f"i = {i}, idx = {idx}, g_seq = {val}")
