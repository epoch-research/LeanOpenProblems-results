def a(n):
    num = factorial(6*n) * (3**n)
    den = factorial(3*n) * factorial(2*n)
    for k in range(1, n+1):
        den *= (2*n + 3*k)
    return num // den

seq = [a(n) for n in range(1, 10)]

# check if it's holonomic
from sage.all import *
print("Ratios:")
for n in range(1, 5):
    print(seq[n]/seq[n-1])
