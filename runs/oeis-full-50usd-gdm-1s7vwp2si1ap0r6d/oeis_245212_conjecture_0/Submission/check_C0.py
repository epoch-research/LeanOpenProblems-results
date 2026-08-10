import sympy
import math

def divisors(m):
    return sympy.divisors(m)

def tau(m):
    return len(divisors(m))

for m in range(3, 10001, 2):
    divs = divisors(m)
    D = m * tau(m) - sum(divs)
    C_prime = sum(c * tau(c) for c in divs if c < m)
    g = math.gcd(D, C_prime)
    C0 = C_prime // g
    D0 = D // g
    # We want to check if C0 is always small.
    # What is the maximum value of C0?
    if C0 > 1:
         # print it
         pass
    # Let's check if (2**(k+1) - 1) divides C0 * (k+1) has any solutions for k >= 1
    for k in range(1, 10):
        if (C0 * (k + 1)) % (2**(k+1) - 1) == 0:
            print(f"m={m}, k={k}: (2^(k+1)-1) divides C0*(k+1) where C0={C0}")
