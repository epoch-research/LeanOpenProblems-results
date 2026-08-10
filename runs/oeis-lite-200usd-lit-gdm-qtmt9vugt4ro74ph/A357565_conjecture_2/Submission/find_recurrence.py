import math
import sympy as sp

def choose(n, k):
    return math.comb(n, k)

def A(n):
    total = 0
    for k in range(n + 1):
        b = choose(n + k - 1, k)
        total += 3 * b**2 + 2 * b**3
    return total

terms = [A(n) for n in range(1, 16)]
print("Terms A(1) to A(15):")
for n, val in enumerate(terms, 1):
    print(f"A({n}) = {val}")

# Let's see if we can fit a recurrence or if it has a simpler representation
