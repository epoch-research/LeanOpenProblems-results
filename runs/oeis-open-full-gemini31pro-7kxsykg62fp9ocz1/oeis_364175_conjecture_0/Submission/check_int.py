import math

for n in range(1, 1000):
    num = math.factorial(6*n) * (3**n)
    den = math.factorial(3*n) * math.factorial(2*n)
    for k in range(1, n+1):
        den *= (2*n + 3*k)
    if num % den != 0:
        print(f"Not an integer for n={n}")
        break
else:
    print("Always an integer up to 999")
