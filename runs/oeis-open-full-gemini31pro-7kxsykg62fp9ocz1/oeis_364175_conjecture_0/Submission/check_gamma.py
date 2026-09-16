import math

def a_int(n):
    num = math.factorial(6*n) * (3**n)
    den = math.factorial(3*n) * math.factorial(2*n)
    for k in range(1, n+1):
        den *= (2*n + 3*k)
    return num // den

def a_real(n):
    num = math.gamma(6*n + 1) * math.gamma(2*n/3 + 1)
    den = math.gamma(3*n + 1) * math.gamma(2*n + 1) * math.gamma(5*n/3 + 1)
    return round(num / den)

for n in range(1, 20):
    if a_int(n) != a_real(n):
        print(f"Mismatch at n={n}: {a_int(n)} != {a_real(n)}")
        exit(0)
print("Match for all n up to 19")
