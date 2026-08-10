import sympy as sp

p = sp.Symbol('p')
k = sp.Symbol('k')

# We want to find R(k) such that:
# R(k) * binom(p+k-1, k)^2 - R(k-1) * binom(p+k-1, k-1)^2 = 3 * binom(p+k-1, k)^2
# Since binom(p+k-1, k-1) = k/(p+k-1) * binom(p+k-1, k)
# We want:
# R(k) - R(k-1) * k^2 / (p+k-1)^2 = 3
# Let R(k) = N(k) / D(k).
# Then:
# N(k)/D(k) - N(k-1)/D(k-1) * k^2 / (p+k-1)^2 = 3
# Let's clear denominators.
# If we choose D(k) = (p+k)^2 * p^2? Or D(k) = (p+k)^2?
# Let's try D(k) = (p+k)^s for s in [0, 1, 2, 3, 4].
# Then D(k-1) = (p+k-1)^s.
# So:
# N(k) / (p+k)^s - N(k-1) * k^2 / (p+k-1)^(s+2) = 3
# If we choose s = 2, then the denominators are (p+k)^2 and (p+k-1)^4.
# Wait! If we choose D(k) = (p+k)^s * (p+k-1)^r?
# Actually, the standard denominator for such recurrence is:
# D(k) = (p+k)^2 or similar.
# Let's search for N_k, D_k such that:
# N_k * D_k_minus_1 * (p+k-1)^2 - N_k_minus_1 * k^2 * D_k = 3 * D_k * D_k_minus_1 * (p+k-1)^2
# We can search for D(k) of the form:
# D(k) = (p+k)^a * k^b * p^c

for a in [0, 1, 2]:
    for b in [0, 1, 2]:
        for c in [0, 1, 2]:
            D_k = (p+k)**a * k**b * p**c
            D_k_minus_1 = (p+k-1)**a * (k-1)**b * p**c
            
            for deg in range(5):
                coeffs = [sp.Symbol(f'c_{i}') for i in range(deg + 1)]
                N_k = sum(coeffs[i] * k**i for i in range(deg + 1))
                N_k_minus_1 = sum(coeffs[i] * (k - 1)**i for i in range(deg + 1))
                
                lhs = N_k * D_k_minus_1 * (p+k-1)**2 - N_k_minus_1 * D_k * k**2
                rhs = 3 * D_k * D_k_minus_1 * (p+k-1)**2
                
                expr = sp.expand(lhs - rhs)
                diff = sp.poly(expr, k)
                eqs = diff.coeffs()
                
                # We need all coefficients to be 0 for all p.
                # So we can solve the system of equations.
                sol = sp.solve(eqs, coeffs)
                if sol:
                    # Let's check if the solution is valid (meaning expr becomes identically 0)
                    test_expr = expr.subs(sol)
                    if sp.simplify(test_expr) == 0:
                        print(f"Found solution for D(k) = (p+k)^{a} * k^{b} * p^{c}, deg(N) = {deg}:")
                        R_k = N_k / D_k
                        print(f"  R(k) = {sp.factor(R_k.subs(sol))}")
                        import sys
                        sys.exit(0)

print("No rational solution found.")
