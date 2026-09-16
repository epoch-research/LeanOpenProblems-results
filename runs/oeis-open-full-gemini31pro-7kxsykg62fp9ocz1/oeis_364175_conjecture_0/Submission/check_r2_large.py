import math

def a(n):
    num = math.factorial(6*n) * (3**n)
    den = math.factorial(3*n) * math.factorial(2*n)
    for k in range(1, n+1):
        den *= (2*n + 3*k)
    return num // den

p = 5
r = 2
for n in range(1, 30):
    v1 = a(n * p**r)
    v2 = a(n * p**(r-1))
    mod = p**(3*r)
    if v1 % mod != v2 % mod:
        print(f"Counterexample! p={p}, r={r}, n={n}")
        exit(0)
print("Checked p=5, r=2, n up to 29")
