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
for n in range(100, 200):
    a_npr = a(n * p)
    a_npr1 = a(n)
    mod = p**3
    if a_npr % mod != a_npr1 % mod:
        print(f"Counterexample! p={p}, n={n}, r={r}")
        sys.exit(0)
print("No counterexamples.")
