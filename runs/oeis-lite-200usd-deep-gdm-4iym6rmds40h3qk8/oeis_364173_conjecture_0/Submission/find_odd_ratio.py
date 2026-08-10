import sympy
from sympy import Symbol

k = Symbol('k')

# a(2k+1) = (4k+2)! (9k+4)! 4^(6k+3) / ( (8k+4)! (2k+1)! (3k+1)! )
# We want to find ratio a(2k+3) / a(2k+1)
# For a(2k+3), replace k with k+1:
# a(2k+3) = (4k+6)! (9k+13)! 4^(6k+9) / ( (8k+12)! (2k+3)! (3k+4)! )

num = 1
for i in range(3, 7):
    num *= (4*k + i)
for i in range(5, 14):
    num *= (9*k + i)
num *= 4**6

den = 1
for i in range(5, 13):
    den *= (8*k + i)
den *= (2*k + 2) * (2*k + 3)
for i in range(2, 5):
    den *= (3*k + i)

ratio = sympy.simplify(num / den)
print("odd ratio =", ratio)
