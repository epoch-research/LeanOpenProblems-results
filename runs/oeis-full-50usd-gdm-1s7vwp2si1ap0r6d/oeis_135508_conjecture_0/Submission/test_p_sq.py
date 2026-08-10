def lcm(a, b):
    import math
    return abs(a*b) // math.gcd(a, b)

x = [0, 1]
for n in range(2, 200):
    val = 2 * x[-1] + lcm(x[-1], n)
    x.append(val)

import sympy
for p in sympy.primerange(2, 13):
    idx = p**2 - 1
    val = x[idx]
    divides = (val % (p**2) == 0)
    print(f"p = {p}, x({idx}) % {p**2} == 0: {divides}")
