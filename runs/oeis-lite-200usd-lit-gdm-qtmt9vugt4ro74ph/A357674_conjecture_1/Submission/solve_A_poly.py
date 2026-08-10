import sympy as sp

p = sp.Symbol('p')
k = sp.Symbol('k')

for d in range(8):
    coeffs = [sp.Symbol(f'c_{i}') for i in range(d + 1)]
    A_k = sum(coeffs[i] * k**i for i in range(d + 1))
    A_k_minus_1 = sum(coeffs[i] * (k - 1)**i for i in range(d + 1))
    
    lhs = A_k * (p+k-1)**2 - A_k_minus_1 * k**2
    rhs = 3 * p**2 * (p+k-1)**2
    
    diff = sp.poly(lhs - rhs, k)
    eqs = diff.coeffs()
    
    sol = sp.solve(eqs, coeffs)
    if sol:
        print(f"Found polynomial solution for degree {d}:")
        print(f"  A(k) = {sp.factor(A_k.subs(sol))}")
        break
else:
    print("No polynomial solution found.")
