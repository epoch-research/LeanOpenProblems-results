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

P1, F1 = dc(2, 1194649)
P2, F2 = dc(1194649, 1194650)
P3, F3 = dc(1194650, 1194651)

F1_val = F1
P12 = P1 * P2
F12 = F1 * P2 + P1 * F2
P123 = P12 * P3
F123 = F12 * P3 + P12 * F3

F_3 = F123
F_2 = F12
F_1 = F1_val

def xgcd(a, b):
    x0, x1, y0, y1 = 1, 0, 0, 1
    while b != 0:
        q, a, b = a // b, b, a % b
        x0, x1 = x1, x0 - q * x1
        y0, y1 = y1, y0 - q * y1
    return a, x0, y0

print("Computing xgcd 1...")
g1, u1, v1 = xgcd(F_2, F_1)
print("Computing xgcd 2...")
g2, u2, v2 = xgcd(F_3, F_2)

print(g1 == g2)
