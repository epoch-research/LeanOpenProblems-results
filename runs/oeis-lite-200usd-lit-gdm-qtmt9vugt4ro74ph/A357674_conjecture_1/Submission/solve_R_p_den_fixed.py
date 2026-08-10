import sympy as sp

p = sp.Symbol('p')
k = sp.Symbol('k')

for j in [0, 1, 2, 3, 4]:
    for s in [0, 1, 2, 3]:
        for deg in range(6):
            coeffs = [sp.Symbol(f'c_{i}') for i in range(deg + 1)]
            N_k = sum(coeffs[i] * k**i for i in range(deg + 1))
            N_k_minus_1 = sum(coeffs[i] * (k - 1)**i for i in range(deg + 1))
            
            lhs = N_k * (p+k-1)**s * (p+k-1)**2 - N_k_minus_1 * (p+k)**s * k**2
            rhs = 3 * p**j * (p+k)**s * (p+k-1)**s * (p+k-1)**2
            num = sp.expand(lhs - rhs)
            
            diff = sp.poly(num, k)
            eqs = diff.coeffs()
            
            sol = sp.solve(eqs, coeffs)
            if sol:
                test_expr = num.subs(sol)
                if sp.simplify(test_expr) == 0:
                    print(f"Found solution for j={j}, s={s}, deg={deg}:")
                    print(f"  R(k) = {sp.factor((N_k / (p**j * (p+k)**s)).subs(sol))}")
                    import sys
                    sys.exit(0)

print("No solution found.")
