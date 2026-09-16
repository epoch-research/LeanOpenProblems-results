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

print(a(25) % 15625)
print(a(5) % 15625)
