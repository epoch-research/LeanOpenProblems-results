import sympy as sp

n, k = sp.symbols('n k')

coeffs_dict = {}
P_expr = 0
for i in range(4): # k degree up to 3
    for j in range(6): # n degree up to 5
        coef = sp.Symbol(f'coeff_{i}_{j}')
        coeffs_dict[coef] = (i, j)
        P_expr += coef * (k**i) * (n**j)

# Correct ratio = F(n, k+1) / F(n, k) = (n-k)*(2n+k)/((k+1)*(n+k+1))
# Let's verify and solve!
# R(k) = (k * P(n, k)) / ((k+n)*(k+2n-2)*(k+2n-1))
# We want to solve:
# F(n, k+1) R(k+1) - F(n, k) R(k) = LHS_terms * F(n, k)
# Dividing by F(n, k):
# ratio * R(k+1) - R(k) = LHS_terms
# Where LHS_terms is the term inside the recurrence sum.
