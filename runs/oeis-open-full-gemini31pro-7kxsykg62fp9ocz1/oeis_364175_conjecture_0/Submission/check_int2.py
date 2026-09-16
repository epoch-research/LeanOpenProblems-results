import math

def a_real_exact(n):
    # compute exact values of Gamma using factorials where possible
    # Gamma(k/3 + 1)
    pass

def check_int(n):
    num = math.factorial(6*n) * (3**n)
    den = math.factorial(3*n) * math.factorial(2*n)
    for k in range(1, n+1):
        den *= (2*n + 3*k)
    return num, den

for n in range(1, 100):
    num, den = check_int(n)
    if num % den != 0:
        print(f"Not an integer for n={n}")
        break
else:
    print("Always an integer up to 99")
