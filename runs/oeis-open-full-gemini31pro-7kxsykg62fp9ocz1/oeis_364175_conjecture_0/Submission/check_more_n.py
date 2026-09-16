import math
import sys
sys.set_int_max_str_digits(2000000)

def a(n):
    num = math.factorial(6*n) * (3**n)
    den = math.factorial(3*n) * math.factorial(2*n)
    for k in range(1, n+1):
        den *= (2*n + 3*k)
    return num // den

p = 5
r = 1
mod = p**(3*r)
# We can compute modulo mod directly to be fast.
# Wait, computing modulo mod during the factorial is not directly possible due to divisions.
# But we can just use Python's big ints, it's fast enough for n=2000.
for n in range(1, 2000):
    v1 = a(n * p**r)
    v2 = a(n * p**(r-1))
    if v1 % mod != v2 % mod:
        print(f"Counterexample! p={p}, r={r}, n={n}")
        sys.exit(0)
print("Checked p=5, r=1 up to n=1999")
