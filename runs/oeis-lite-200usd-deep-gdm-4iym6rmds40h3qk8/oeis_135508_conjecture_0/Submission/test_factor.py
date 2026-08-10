def lcm(a, b):
    import math
    return abs(a*b) // math.gcd(a, b)

x = [0, 1]
for n in range(1, 35):
    x.append(2 * x[-1] + lcm(x[-1], n + 1))

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
    return factors

for n in range(1, 30):
    print(f"x_{n} = {x[n]} = {prime_factors(x[n])}")
