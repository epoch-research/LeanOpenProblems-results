import sympy
from sympy import Symbol, binomial

def A108625(n, k):
    return sum(binomial(n, i)**2 * binomial(n + k - i, k - i) for i in range(k + 1))

def A(n):
    return sum(binomial(n, k)**2 * binomial(n + k, k) * A108625(n, n - k) for k in range(n + 1))

# Generate the first 12 terms
terms = [A(n) for n in range(12)]
print("Terms:", terms)

# Let's search for a recurrence:
# c3(n) A(n+3) + c2(n) A(n+2) + c1(n) A(n+1) + c0(n) A(n) = 0
# where ci(n) are polynomials in n of some degree d.
# Let's try to find a recurrence of order 2:
# (a2 * n^2 + b2 * n + c2) A(n+2) + (a1 * n^2 + b1 * n + c1) A(n+1) + (a0 * n^2 + b0 * n + c0) A(n) = 0
# Let's write a solver for this.

from sympy import solve, symbols

def find_recurrence(terms, order, degree):
    n_vars = (order + 1) * (degree + 1)
    coeffs = symbols(f'co0:{n_vars}')
    
    # We want to solve for coeffs such that for all n:
    # sum_{i=0}^order (sum_{j=0}^degree coeff_{i,j} n^j) terms[n+i] = 0
    equations = []
    for n_val in range(len(terms) - order):
        expr = 0
        idx = 0
        for i in range(order + 1):
            poly = 0
            for j in range(degree + 1):
                poly += coeffs[idx] * (n_val ** j)
                idx += 1
            expr += poly * terms[n_val + i]
        equations.append(expr)
        
    sol = solve(equations, coeffs)
    return sol

for order in [2, 3]:
    for degree in [2, 3, 4, 5]:
        sol = find_recurrence(terms, order, degree)
        if sol:
            # check if non-trivial
            if any(v != 0 for v in sol.values()):
                print(f"Found recurrence of order {order}, degree {degree}:")
                print(sol)
                break
