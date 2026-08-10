def lcm(a, b):
    import math
    return abs(a*b) // math.gcd(a, b)

x = [0, 1]
for n in range(2, 200):
    val = 2 * x[-1] + lcm(x[-1], n)
    x.append(val)

print("x(14) % 15 =", x[14] % 15)
print("x(20) % 21 =", x[20] % 21)
print("x(33) % 35 =", x[33] % 35)
