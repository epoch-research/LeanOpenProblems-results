import sympy as sp

p = sp.Symbol('p')
k = sp.Symbol('k')

for d in range(8):
    coeffs = [sp.Symbol(f'c_{i}') for i in range(d + 1)]
    # We want A_k as a polynomial in k with coefficients in Q(p).
    A_k = sum(coeffs[i] * k**i for i in range(d + 1))
    A_k_minus_1 = sum(coeffs[i] * (k - 1)**i for i in range(d + 1))
    
    lhs = A_k * (p+k-1)**2 - A_k_minus_1 * k**2
    rhs = 3 * (p+k-1)**2 # we want R_k - R_{k-1} k^2 / (p+k-1)^2 = 3, so R_k (p+k-1)^2 - R_{k-1} k^2 = 3 (p+k-1)^2
    
    expr = sp.expand(lhs - rhs)
    poly_k = sp.poly(expr, k)
    eqs = poly_k.coeffs()
    
    # We want to solve eqs for the coeffs in Q(p).
    sol = sp.solve(eqs, coeffs)
    if sol:
        # Check if the solution actually makes the expression 0
        test = expr.subs(sol)
        if sp.simplify(test) == 0:
            print(f"Found polynomial solution for degree {d}:")
            print(f"  R(k) = {sp.factor(A_k.subs(sol))}")
            break
else:
    print("No polynomial solution found.")
