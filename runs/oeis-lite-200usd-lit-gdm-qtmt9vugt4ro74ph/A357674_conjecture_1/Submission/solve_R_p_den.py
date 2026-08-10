import sympy as sp

p = sp.Symbol('p')
k = sp.Symbol('k')

for j in [1, 2, 3, 4]:
    for s in [0, 1, 2, 3]:
        for deg in range(6):
            coeffs = [sp.Symbol(f'c_{i}') for i in range(deg + 1)]
            N_k = sum(coeffs[i] * k**i for i in range(deg + 1))
            N_k_minus_1 = sum(coeffs[i] * (k - 1)**i for i in range(deg + 1))
            
            D_k = p**j * (p+k)**s
            D_k_minus_1 = p**j * (p+k-1)**s
            
            R_k = N_k / D_k
            R_k_minus_1 = N_k_minus_1 / D_k_minus_1
            
            expr = R_k * (p+k-1)**2 - R_k_minus_1 * k**2 - 3 * (p+k-1)**2
            num, den = sp.fraction(sp.simplify(expr))
            
            num = sp.expand(num)
            diff = sp.poly(num, k)
            eqs = diff.coeffs()
            
            sol = sp.solve(eqs, coeffs)
            if sol:
                test_expr = expr.subs(sol)
                if sp.simplify(test_expr) == 0:
                    print(f"Found solution for j={j}, s={s}, deg={deg}:")
                    print(f"  R(k) = {sp.factor(R_k.subs(sol))}")
                    import sys
                    sys.exit(0)

print("No solution found with p^j in denominator.")
