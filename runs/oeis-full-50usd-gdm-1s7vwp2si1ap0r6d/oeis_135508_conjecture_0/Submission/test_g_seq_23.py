def lcm(a, b):
    import math
    return abs(a*b) // math.gcd(a, b)

x = [0, 1]
for n in range(2, 500):
    val = 2 * x[-1] + lcm(x[-1], n)
    x.append(val)

import math
g = [1]
q = 23
for i in range(1, 5):
    val = math.gcd(x[g[-1] * (q - 2) - 1], g[-1] * (q - 2))
    g.append(val)

print("g_seq(23, i):", g)
