import math
import sys

sys.set_int_max_str_digits(20000000)

def dc(a, b):
    if b <= a:
        return 1, 0
    if b == a + 1:
        return a, (1 if a % 2 == 0 else -1)
    m = (a + b) // 2
    p1, f1 = dc(a, m)
    p2, f2 = dc(m, b)
    return p1 * p2, f1 * p2 + p1 * f2

print("Computing F_1...")
P1, F1 = dc(2, 1194649)
print("F_1 done.")
