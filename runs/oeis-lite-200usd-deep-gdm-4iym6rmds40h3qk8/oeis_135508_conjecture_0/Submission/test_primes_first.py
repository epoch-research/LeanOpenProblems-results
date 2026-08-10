def lcm(a, b):
    import math
    return abs(a*b) // math.gcd(a, b)

import math

x = [0, 1]
for n in range(1, 1000):
    g = math.gcd(x[-1], n + 1)
    mult = 2 + (n + 1) // g
    x.append(x[-1] * mult)

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.sqrt(n)) + 1):
        if n % i == 0: return False
    return True

primes = [p for p in range(2, 200) if is_prime(p)]
for p in primes:
    first_n = None
    for n in range(1, 1000):
        if x[n] % p == 0:
            first_n = n
            break
    print(f"p = {p:3d}: first_n = {first_n}")
