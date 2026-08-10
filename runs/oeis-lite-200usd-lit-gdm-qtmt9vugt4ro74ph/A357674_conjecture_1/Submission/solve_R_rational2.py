import sympy as sp

p = sp.Symbol('p')
k = sp.Symbol('k')

for a in [0, 1, 2]:
    for b in [0, 1, 2]:
        D_k = p**a * (p+k)**b
        D_k_minus_1 = p**a * (p+k-1)**b
        
        for deg in range(5):
            coeffs = [sp.Symbol(f'c_{i}') for i in range(deg + 1)]
            N_k = sum(coeffs[i] * k**i for i in range(deg + 1))
            N_k_minus_1 = sum(coeffs[i] * (k - 1)**i for i in range(deg + 1))
            
            lhs = N_k * D_k_minus_1 * (p+k-1)**2 - N_k_minus_1 * D_k * k**2
            rhs = 3 * D_k * D_k_minus_1 * (p+k-1)**2
            
            expr = sp.expand(lhs - rhs)
            diff = sp.poly(expr, k)
            eqs = diff.coeffs()
            
            sol = sp.solve(eqs, coeffs)
            if sol:
                print(f"Found solution for a={a}, b={b}, deg={deg}:")
                R_k = N_k / D_k
                print(f"  R(k) = {sp.factor(R_k.subs(sol))}")
                import sys
                sys.exit(0)
print("No solution found.")
