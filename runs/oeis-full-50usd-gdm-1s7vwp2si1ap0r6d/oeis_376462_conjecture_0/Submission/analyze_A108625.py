import sympy
from sympy import binomial, Symbol

n = Symbol('n', integer=True)
k = Symbol('k', integer=True)

# Print a table of A108625(n, k) for n, k in [0..4]
for i in range(5):
    row = []
    for j in range(5):
        # A108625(i, j)
        val = sum(binomial(i, s)**2 * binomial(i + j - s, j - s) for s in range(j + 1))
        row.append(int(val))
    print(f"n={i}: {row}")
