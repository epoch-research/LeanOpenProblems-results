def lcm(a, b):
    import math
    return abs(a*b) // math.gcd(a, b)

x = [0, 1]
for n in range(2, 200):
    val = 2 * x[-1] + lcm(x[-1], n)
    x.append(val)

print("x(9) % 9 =", x[9] % 9)
print("x(15) % 15 =", x[15] % 15)
print("x(21) % 21 =", x[21] % 21)
print("x(35) % 35 =", x[35] % 35)
