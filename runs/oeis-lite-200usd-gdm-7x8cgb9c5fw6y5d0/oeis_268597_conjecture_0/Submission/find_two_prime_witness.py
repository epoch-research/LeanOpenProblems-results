import sympy

def phi(n):
    return sympy.totient(n)

# Let's search for a general formula for x given m = A * B where A, B >= 5 are coprime.
# We want (x - 1) % phi(x) == n = m - 1
# Let's try to test different functions of A and B:
# 1) x = A^2 * B^2?
# 2) x = A^2 * B?
# 3) x = A * B^2?
# 4) x = (A-1)*(B-1)? No, needs x > 0 and (x-1) % phi(x) == n
# Let's test combinations of A^a * B^b * (some small factor)
# Or other expressions in terms of A and B.

m = 35 # 5 * 7, A=5, B=7
A = 5
B = 7
n = 34

# Let's search over all x of the form (A-1)*(B-1)*c + d, etc.
# Actually, let's just search for any small x and analyze its prime factors in terms of A and B.
for x in range(1, 10000):
    if (x - 1) % phi(x) == n:
        print(f"For m=35: x={x} works, factors of x: {sympy.factorint(x)}, phi(x)={phi(x)}")

m = 55 # 5 * 11, A=5, B=11
n = 54
for x in range(1, 20000):
    if (x - 1) % phi(x) == n:
        print(f"For m=55: x={x} works, factors of x: {sympy.factorint(x)}, phi(x)={phi(x)}")
