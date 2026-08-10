import sympy
from sympy import binomial

# Let's search for combinations of binomial coefficients of the form binomial(a*k, b*k)
# whose product or ratio is equal to a(2k) for k = 1, 2.
# Possible arguments for binomial are multiples of k from 1 to 18.

k_val = 1
val1 = int(sympy.factorial(18*k_val) * sympy.factorial(4*k_val) * sympy.factorial(3*k_val) / (sympy.factorial(9*k_val) * sympy.factorial(8*k_val) * sympy.factorial(6*k_val) * sympy.factorial(2*k_val)))

k_val = 2
val2 = int(sympy.factorial(18*k_val) * sympy.factorial(4*k_val) * sympy.factorial(3*k_val) / (sympy.factorial(9*k_val) * sympy.factorial(8*k_val) * sympy.factorial(6*k_val) * sympy.factorial(2*k_val)))

# We can express a(2k) as a product/ratio of factorials: (18k)! (4k)! (3k)! / ((9k)! (8k)! (6k)! (2k)!)
# Let's factor this using primes
print("k=1 factors:", sympy.factorint(val1))
print("k=2 factors:", sympy.factorint(val2))
