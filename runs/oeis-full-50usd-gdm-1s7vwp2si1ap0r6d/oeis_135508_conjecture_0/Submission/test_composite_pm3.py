def lcm(a, b):
    import math
    return abs(a*b) // math.gcd(a, b)

x = [0, 1]
for n in range(2, 200):
    val = 2 * x[-1] + lcm(x[-1], n)
    x.append(val)

import sympy
for q in sympy.primerange(5, 100):
    if not sympy.isprime(q-2):
        divides = (x[q-3] % (q-2) == 0)
        print(f"q = {q}, q-2 = {q-2}, x(q-3) % (q-2) == 0: {divides}")
