import math

def check_int(n):
    num = math.factorial(6*n) * (3**n)
    den = math.factorial(3*n) * math.factorial(2*n)
    for k in range(1, n+1):
        den *= (2*n + 3*k)
    return num % den == 0

for n in range(1, 10000):
    if not check_int(n):
        print(f"NOT AN INTEGER AT n={n}")
        break
else:
    print("Always an integer up to 9999")
