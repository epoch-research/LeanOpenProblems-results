import sys
from fractions import Fraction
from math import gcd

def bernoulli(n):
    A = [0] * (n + 1)
    for m in range(n + 1):
        A[m] = Fraction(1, m + 1)
        for j in range(m, 0, -1):
            A[j - 1] = j * (A[j - 1] - A[j])
    return A[0]

def a(n):
    if n == 0: return 1
    B = bernoulli(2 * n)
    d = 2 * n * (2 * n - 1)
    val = B / d
    return val.denominator

import sympy
for n in range(1, 100):
    val = a(n)
    p = val // 12
    if val % 12 == 0 and sympy.isprime(p):
        print(f"n={n}, p={p}")

