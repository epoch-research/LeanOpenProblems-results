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

primes = [p for p in range(2, 1000) if is_prime(p)]
matching_primes = []
for p in primes:
    if x[p-1] % p == 0:
        matching_primes.append(p)

print("Primes p such that p | x_seq(p - 1):")
print(matching_primes)
