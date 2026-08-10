def lcm(a, b):
    import math
    return abs(a*b) // math.gcd(a, b)

x = [0, 1]
for n in range(2, 200):
    val = 2 * x[-1] + lcm(x[-1], n)
    x.append(val)

print("x(0..10):", x[:11])

# Check if q | x(q^2 - 1) for primes q
import sympy
for q in sympy.primerange(2, 13):
    idx = q**2 - 1
    divides = (x[idx] % q == 0)
    print(f"q = {q}, q^2 - 1 = {idx}, x(idx) % q == 0: {divides}")
