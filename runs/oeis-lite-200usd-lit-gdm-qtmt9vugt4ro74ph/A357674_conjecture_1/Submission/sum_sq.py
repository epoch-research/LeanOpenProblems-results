import sympy as sp

n = sp.Symbol('n', integer=True)
j = sp.Symbol('j', integer=True)
m = n - 1
N = 3 * n - 1

# Let's compute the sum of binomial(j, m)**2 for j from m to N
# We can use sympy's summation function
term = sp.binomial(j, m)**2
sum_expr = sp.summation(term, (j, m, N))
print("Sum expression:")
print(sum_expr)
