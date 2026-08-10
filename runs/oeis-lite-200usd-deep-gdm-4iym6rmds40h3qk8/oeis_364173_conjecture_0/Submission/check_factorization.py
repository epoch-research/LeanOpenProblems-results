import sympy
from sympy import factorint

def a(n):
    import math
    # since we want integer values for small n, we can use exact factorial ratios
    # for even n: (18k)! (4k)! (3k)! / ( (9k)! (8k)! (6k)! (2k)! ) where n = 2k
    # for odd n: (4k+2)! (9k+4)! 4^(6k+3) / ( (8k+4)! (2k+1)! (3k+1)! ) where n = 2k+1
    if n % 2 == 0:
        k = n // 2
        num = math.factorial(18*k) * math.factorial(4*k) * math.factorial(3*k)
        den = math.factorial(9*k) * math.factorial(8*k) * math.factorial(6*k) * math.factorial(2*k)
    else:
        k = n // 2
        num = math.factorial(4*k+2) * math.factorial(9*k+4) * (4**(6*k+3))
        den = math.factorial(8*k+4) * math.factorial(2*k+1) * math.factorial(3*k+1)
    return num // den

for p in [5, 7]:
    for n in [1, 2]:
        val1 = a(n * p)
        val2 = a(n)
        diff = val1 - val2
        print(f"p={p}, n={n}: factorint(diff) = {factorint(diff)}")
