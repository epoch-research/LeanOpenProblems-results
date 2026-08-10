import sympy as sp

p = sp.Symbol('p')
for j in range(1, 5):
    expr = sp.binomial(2*p + j - 1, p + j)
    # let's get the series expansion around p = 0 up to p^5
    expr_ser = sp.series(expr, p, 0, 6)
    print(f"j = {j} (k = p + {j}):")
    print(f"  {expr_ser}")

