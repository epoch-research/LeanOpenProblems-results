import sympy as sp

a = sp.Symbol('a')
P = 1
for i in range(16):
    P *= (a + i)

F_even = 0
for i in range(16):
    sign = 1 if i % 2 == 0 else -1
    F_even += sign * P // (a + i)

def to_horner(poly, var):
    poly = sp.Poly(poly, var)
    coeffs = poly.all_coeffs()
    res = str(coeffs[0])
    for c in coeffs[1:]:
        res = f"({res}) * a + {c}"
    return res

P_horner = to_horner(P, a)
F_horner = to_horner(F_even, a)

print("def P16 (a : ℤ) : ℤ :=")
print("  " + P_horner)
print("def F16_even (a : ℤ) : ℤ :=")
print("  " + F_horner)
