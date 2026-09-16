import math
import sys
sys.set_int_max_str_digits(10000)

def a(n):
    num = math.factorial(6*n) * (3**n)
    den = math.factorial(3*n) * math.factorial(2*n)
    for k in range(1, n+1):
        den *= (2*n + 3*k)
    return num // den

print("a(25) % 1953125 = ", a(25) % 1953125)
print("a(125) % 1953125 = ", a(125) % 1953125)
