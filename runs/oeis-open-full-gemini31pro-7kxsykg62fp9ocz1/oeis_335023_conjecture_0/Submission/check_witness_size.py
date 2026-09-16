import sys
import gmpy2
import time

sys.set_int_max_str_digits(20000000)
gmpy2.get_context().precision = 20000000

def dc(a, b):
    if b <= a:
        return 1, 0
    if b == a + 1:
        return a, (1 if a % 2 == 0 else -1)
    m = (a + b) // 2
    p1, f1 = dc(a, m)
    p2, f2 = dc(m, b)
    return p1 * p2, f1 * p2 + p1 * f2

P1, F1 = dc(2, 1000)

G = gmpy2.gcd(F1, P1)
mA = F1 // G
mB = P1 // G

print("Digits of F1:", len(str(F1)))
print("Digits of G:", len(str(G)))
print("Digits of mA:", len(str(mA)))
print("Digits of mB:", len(str(mB)))

g, u, v = gmpy2.gcdext(mA, mB)
print("Digits of u:", len(str(u)))
print("Digits of v:", len(str(v)))
