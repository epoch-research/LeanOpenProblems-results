def lcm(a, b):
    import math
    return abs(a*b) // math.gcd(a, b)

import math

x = [0, 1]
def lcm(a, b):
    import math
    return abs(a*b) // math.gcd(a, b)

import math

x = [0, 1]
for n in range(1, 100):
    g = math.gcd(x[-1], n + 1)
    mult = 2 + (n + 1) // g
    x.append(x[-1] * mult)

# Check if there is any prime p >= 3 and any n >= 1 such that:
# p divides x[n+1] and p divides n+1, but p does not divide x[n]

def prime_factors(n):
    i = 2
    factors = []
    while i * i <= n:
        if n % i:
            i += 1
        else:
            n //= i
            factors.append(i)
    if n > 1:
        factors.append(n)
    return set(factors)

found = False
for n in range(1, 99):
    # n+1 is the index
    # We want to check if any prime factor of gcd(x[n+1], n+1) does not divide x[n]
    p_factors = prime_factors(math.gcd(x[n+1], n+1))
    for p in p_factors:
        if p >= 3 and x[n] % p != 0:
            print(f"FOUND: p={p}, n+1={n+1}, x_{n+1}={x[n+1]}, x_{n}={x[n]}")
            found = True

if not found:
    print("NO EXAMPLES FOUND! The claim 'p divides x_{n+1} and n+1 => p divides x_n' is TRUE for p >= 3!")

