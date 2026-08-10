import sympy
from sympy import binomial, Symbol

k = Symbol('k', integer=True, positive=True)

# Let's check if we can write a(2k) as products of binomial coefficients
# a(2k) = (18k)! * (4k)! * (3k)! / ((9k)! * (8k)! * (6k)! * (2k)!)
# Let's test a few combinations
for k_val in range(1, 5):
    val = int(sympy.factorial(18*k_val) * sympy.factorial(4*k_val) * sympy.factorial(3*k_val) / (sympy.factorial(9*k_val) * sympy.factorial(8*k_val) * sympy.factorial(6*k_val) * sympy.factorial(2*k_val)))
    print(f"a(2*{k_val}) = {val}")
