import sympy as sp

a = sp.Symbol('a')
P = 1
for i in range(16):
    P *= (a + i)

F_even = 0
for i in range(16):
    sign = 1 if i % 2 == 0 else -1
    F_even += sign * P // (a + i)

P_exp = sp.expand(P)
F_even_exp = sp.expand(F_even)

print("P =", P_exp)
print("F_even =", F_even_exp)
