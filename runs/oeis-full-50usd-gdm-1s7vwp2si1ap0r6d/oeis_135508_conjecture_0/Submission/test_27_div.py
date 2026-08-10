def lcm(a, b):
    import math
    return abs(a*b) // math.gcd(a, b)

x = [0, 1]
for n in range(2, 200):
    val = 2 * x[-1] + lcm(x[-1], n)
    x.append(val)

print("x(27) % 11 =", x[27] % 11)
