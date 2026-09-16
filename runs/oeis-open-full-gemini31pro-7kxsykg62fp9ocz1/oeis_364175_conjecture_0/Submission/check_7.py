import math

def a(n):
    num = math.factorial(6*n) * (3**n)
    den = math.factorial(3*n) * math.factorial(2*n)
    for k in range(1, n+1):
        den *= (2*n + 3*k)
    return num // den

p = 7
print(f"a(1) = {a(1)}")
print(f"a(7) = {a(7)}")
print(f"a(7) % 343 = {a(7) % 343}")
print(f"a(1) % 343 = {a(1) % 343}")
