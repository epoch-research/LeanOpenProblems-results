import sympy as sp
p = sp.Symbol('p')
k = sp.Symbol('k')
c_0 = sp.Symbol('c_0')

D_k = p
D_k_minus_1 = p
N_k = c_0
N_k_minus_1 = c_0

lhs = N_k * D_k_minus_1 * (p+k-1)**2 - N_k_minus_1 * D_k * k**2
rhs = 3 * D_k * D_k_minus_1 * (p+k-1)**2

expr = sp.expand(lhs - rhs)
diff = sp.poly(expr, k)
eqs = diff.coeffs()
print("eqs:", eqs)
sol = sp.solve(eqs, [c_0])
print("sol:", sol)
