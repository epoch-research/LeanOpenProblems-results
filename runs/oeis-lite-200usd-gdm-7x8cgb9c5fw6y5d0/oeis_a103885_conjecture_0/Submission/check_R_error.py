import sympy as sp

# Let's see what e_sol is and why it's False
from check_symmetry_exact import P_expr, x, m, e
R_expr = sum(e[j] * (x*(1-x))**j for j in range(m+1))
diff_expr = sp.expand(P_expr - R_expr)
e_sol = sp.solve([diff_expr.coeff(x, k) for k in range(2*m+1)], e)
print("e_sol:", e_sol)
remaining_diff = sp.expand(diff_expr.subs(e_sol))
print("Remaining difference after substitution:", remaining_diff)
