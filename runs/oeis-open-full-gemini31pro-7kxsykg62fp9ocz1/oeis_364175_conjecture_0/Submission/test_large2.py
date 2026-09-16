import sys
sys.set_int_max_str_digits(200000)
def a(n):
    num = 1
    den = 1
    for k in range(1, n+1):
        den *= (2*n + 3*k)
    import math
    num *= math.factorial(6*n) * (3**n)
    den *= math.factorial(3*n) * math.factorial(2*n)
    return num // den

p = 5
r = 1
for n in range(100, 500):
    if a(n * p**r) % (p**(3*r)) != a(n * p**(r-1)) % (p**(3*r)):
        print(f"False for p={p}, r={r}, n={n}")
        sys.exit(0)
print("Checked p=5, r=1, n=100..499")
