import sympy as sp

p = sp.Symbol('p')
for k in range(1, 10):
    expr = 1
    for j in range(1, k + 1):
        expr *= (p + j - 1) / j
    expr = sp.expand(expr)
    print(f"k = {k}:")
    print(f"  {expr}")
