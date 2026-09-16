import sys
import gmpy2

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

P1, F1 = dc(2, 1194649)
P2, F2 = dc(1194649, 1194650)
P3, F3 = dc(1194650, 1194651)

F1_val = gmpy2.mpz(F1)
P12 = gmpy2.mpz(P1 * P2)
F12 = gmpy2.mpz(F1 * P2 + P1 * F2)
P123 = gmpy2.mpz(P12 * P3)
F123 = gmpy2.mpz(F12 * P3 + P12 * F3)

F_3 = F123
F_2 = F12
F_1 = F1_val

print("Computing xgcd 1...")
g1, u1, v1 = gmpy2.gcdext(F_2, F_1)
print("Computing xgcd 2...")
g2, u2, v2 = gmpy2.gcdext(F_3, F_2)

print(g1 == g2)
