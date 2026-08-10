import sympy
from sympy import binomial, Symbol, summation

n = Symbol('n', integer=True)
k = Symbol('k', integer=True)
i = Symbol('i', integer=True)

expr = binomial(n, i)**2 * binomial(n + k - i, k - i)
# Let's see if sympy can simplify the sum from i=0 to k
# sympy summation of hypergeometric terms
simp = summation(expr, (i, 0, k))
print("Sympy sum:", simp)
