import sympy as sp

a = sp.Symbol('a')
P = 1
for i in range(16):
    P *= (a + i)

F_even = 0
for i in range(16):
    sign = 1 if i % 2 == 0 else -1
    term = P / (a + i)
    F_even += sign * term

P_exp = sp.expand(P)
F_even_exp = sp.expand(F_even)

print("def P16 (a : ℤ) : ℤ :=")
print("  " + str(P_exp).replace("**", "^"))
print("def F16_even (a : ℤ) : ℤ :=")
print("  " + str(F_even_exp).replace("**", "^"))
