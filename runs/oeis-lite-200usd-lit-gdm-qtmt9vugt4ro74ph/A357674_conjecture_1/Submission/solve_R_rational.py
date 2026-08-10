import sympy as sp

p = sp.Symbol('p')
k = sp.Symbol('k')

# Let's search for R(k) = A(k) / B(k)
# Actually, since the equation is:
# R(k) * (p+k-1)^2 - R(k-1) * k^2 = 3 * (p+k-1)^2
# Let's see if there is a solution with denominator B(k) = k^2 * (p+k-1)^2 or similar.
# Or let's use sympy's solve_recurrence or rsolve if possible.
# Wait, we can write R(k) as a rational function in k.
# Let's try to find R(k) of the form (a*k^2 + b*k + c) / (p^2) or something? No, that has no k in the denominator.
# Let's test if there is a solution of the form:
# R(k) = (c_0 + c_1*k + c_2*k^2 + c_3*k^3) / (p^2 * (p+k)^2) etc.

# Let's write a loop to search for R(k) of the form:
# N(k) / D(k) where D(k) = (p+k)^s or similar.
# Let's try D(k) = p^2 * (p+k)^2, s from 0 to 2.
for s in [0, 1, 2]:
    for deg in range(5):
        coeffs = [sp.Symbol(f'c_{i}') for i in range(deg + 1)]
        N_k = sum(coeffs[i] * k**i for i in range(deg + 1))
        N_k_minus_1 = sum(coeffs[i] * (k - 1)**i for i in range(deg + 1))
        
        D_k = (p+k)**s
        D_k_minus_1 = (p+k-1)**s
        
        R_k = N_k / D_k
        R_k_minus_1 = N_k_minus_1 / D_k_minus_1
        
        # We want: R_k * (p+k-1)^2 - R_k_minus_1 * k^2 - 3 * (p+k-1)^2 = 0
        # Let's clear denominators:
        # R_k = N_k / (p+k)^s
        # R_k_minus_1 = N_k_minus_1 / (p+k-1)^s
        # LHS = N_k * (p+k-1)^(2-s) * (p+k-1)^s - N_k_minus_1 * k^2 * (p+k)^s / ... ?
        # Better:
        expr = R_k * (p+k-1)**2 - R_k_minus_1 * k**2 - 3 * (p+k-1)**2
        expr = sp.simplify(expr)
        num, den = sp.fraction(expr)
        
        num = sp.expand(num)
        diff = sp.poly(num, k)
        eqs = diff.coeffs()
        
        sol = sp.solve(eqs, coeffs)
        if sol:
            print(f"Found solution for s={s}, deg={deg}:")
            print(f"  R(k) = {sp.factor(R_k.subs(sol))}")
            break
