import sympy
from sympy import Symbol

k = Symbol('k')

num = 1
for i in range(1, 19):
    num *= (18*k + i)
for i in range(1, 5):
    num *= (4*k + i)
for i in range(1, 4):
    num *= (3*k + i)

den = 1
for i in range(1, 10):
    den *= (9*k + i)
for i in range(1, 9):
    den *= (8*k + i)
for i in range(1, 7):
    den *= (6*k + i)
den *= (2*k + 1) * (2*k + 2)

ratio = sympy.simplify(num / den)
print("even ratio =", ratio)
