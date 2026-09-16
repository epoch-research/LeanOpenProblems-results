import math
import sys
sys.set_int_max_str_digits(20000000)

def a(n):
    num = math.factorial(6*n) * (3**n)
    den = math.factorial(3*n) * math.factorial(2*n)
    for k in range(1, n+1):
        den *= (2*n + 3*k)
    return num // den

p = 5
mod = p**3
for n in range(1, 10000):
    if a(n * p) % mod != a(n) % mod:
        print(f"Counterexample! p={p}, n={n}")
        sys.exit(0)
print(f"Checked p={p} up to n=9999")
