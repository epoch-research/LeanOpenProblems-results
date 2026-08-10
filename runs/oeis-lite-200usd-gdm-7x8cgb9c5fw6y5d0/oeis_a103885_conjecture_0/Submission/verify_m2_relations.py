import sympy as sp

c_coeffs = [1/1154560, -19/1731840, 37/865920, -1/15744, 1/31488]
d_coeffs = [9/9020, -1313/27060, 26501/54120, -71119/54120, 1]

P_eval_1 = sum(c_coeffs[i] for i in range(5))
Q_eval_1 = sum(d_coeffs[i] for i in range(5))

print("P.eval 1:", P_eval_1)
print("Q.eval 1:", Q_eval_1)
print("LHS (n=1):", 1680 * P_eval_1 * 2064)
print("RHS (n=1):", Q_eval_1 * 16)
