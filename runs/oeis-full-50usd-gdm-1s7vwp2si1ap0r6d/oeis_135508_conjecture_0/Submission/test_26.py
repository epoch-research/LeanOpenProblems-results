def lcm(a, b):
    import math
    return abs(a*b) // math.gcd(a, b)

x = [0, 1]
for n in range(2, 200):
    val = 2 * x[-1] + lcm(x[-1], n)
    x.append(val)

print("x(26) % 9 =", x[26] % 9)
print("x(26) % 27 =", x[26] % 27)
print("gcd(x(26), 27) =", math.gcd(x[26], 27) if 'math' in locals() else __import__('math').gcd(x[26], 27))
