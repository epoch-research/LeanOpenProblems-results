import sympy as sp

p = sp.Symbol('p')
k = sp.Symbol('k')

# X(k) * (p+k-1)^2 - X(k-1) * k^2 = 3 * (p+k-1)^2
# Let's search for X(k) as a polynomial in k of degree d with coefficients as rational functions of p.
for d in range(5):
    coeffs = [sp.Symbol(f'c_{i}') for i in range(d + 1)]
    X_k = sum(coeffs[i] * k**i for i in range(d + 1))
    X_k_minus_1 = sum(coeffs[i] * (k - 1)**i for i in range(d + 1))
    
    lhs = sp.expand(X_k * (p + k - 1)**2 - X_k_minus_1 * k**2)
    rhs = sp.expand(3 * (p + k - 1)**2)
    
    diff = sp.poly(lhs - rhs, k)
    eqs = diff.coeffs()
    
    sol = sp.solve(eqs, coeffs)
    if sol:
        print(f"For S2 (degree {d}): found solution X(k) =")
        sol_X = X_k.subs(sol)
        print(f"  {sol_X}")
        break
else:
    print("For S2: No polynomial solution found.")

# Now for S1:
# Y(k) * (p+k-1) - Y(k-1) * k = 4 * (p+k-1)
for d in range(5):
    coeffs = [sp.Symbol(f'd_{i}') for i in range(d + 1)]
    Y_k = sum(coeffs[i] * k**i for i in range(d + 1))
    Y_k_minus_1 = sum(coeffs[i] * (k - 1)**i for i in range(d + 1))
    
    lhs = sp.expand(Y_k * (p + k - 1) - Y_k_minus_1 * k)
    rhs = sp.expand(4 * (p + k - 1))
    
    diff = sp.poly(lhs - rhs, k)
    eqs = diff.coeffs()
    
    sol = sp.solve(eqs, coeffs)
    if sol:
        print(f"For S1 (degree {d}): found solution Y(k) =")
        sol_Y = Y_k.subs(sol)
        print(f"  {sol_Y}")
        break
else:
    print("For S1: No polynomial solution found.")

