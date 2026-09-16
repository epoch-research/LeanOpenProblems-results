import sys
sys.set_int_max_str_digits(2000000)
import math

def a(n):
    num = math.factorial(6*n) * (3**n)
    den = math.factorial(3*n) * math.factorial(2*n)
    for k in range(1, n+1):
        den *= (2*n + 3*k)
    return num // den

p = 101
r = 1
mod = p**(3*r)
for n in range(1, 10):
    v1 = a(n * p**r)
    v2 = a(n * p**(r-1))
    if v1 % mod != v2 % mod:
        print(f"Counterexample! p={p}, r={r}, n={n}")
        exit(0)
print("Checked p=101")
