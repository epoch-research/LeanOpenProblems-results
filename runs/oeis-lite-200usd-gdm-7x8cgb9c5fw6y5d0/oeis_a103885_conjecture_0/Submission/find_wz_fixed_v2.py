import sympy as sp

n, k = sp.symbols('n k')

# Let's define the recurrence coefficients
P_n = 5*n**2 - 5*n + 1
P_neg_n = 5*n**2 + 5*n + 1
Q_n = 220*n**4 - 136*n**2 + 12

alpha2 = (2*n + 1)*(2*n + 2) * P_n
alpha1 = - Q_n
alpha0 = -(2*n - 1)*(2*n - 2) * P_neg_n

# Term ratios
# F(n+1, k) / F(n, k)
ratio_np1 = (n + 1) * (2*n + k + 1) * (2*n + k) / ((n + 1 - k) * n * (n + k + 1))
# F(n-1, k) / F(n, k)
ratio_nm1 = (n - k) * (n - 1) * (n + k) / (n * (2*n + k - 1) * (2*n + k - 2))
# F(n, k+1) / F(n, k)
ratio_kp1 = (n - k) * (2*n + k) / ((k + 1) * (n + k + 1))

# LHS of the WZ equation: alpha2 * ratio_np1 + alpha1 + alpha0 * ratio_nm1
# Let's find a common denominator for LHS
# Let's write R(n, k) = k * S(n, k) / (n * (2*n + k - 2) * (2*n + k - 1) * (n + k))
# Then we want: ratio_kp1 * R(n, k+1) - R(n, k) = LHS
# Let's expand this and see if we can find a polynomial S(n, k).

# We define S(n, k) as a general polynomial in n and k
coeffs = {}
S = 0
for i in range(5): # k degree up to 4
    for j in range(5): # n degree up to 4
        c = sp.Symbol(f'c_{i}_{j}')
        coeffs[c] = (i, j)
        S += c * k**i * n**j

# Define R(n, k)
def R_func(k_val):
    return k_val * S.subs(k, k_val) / (n * (2*n + k_val - 2) * (2*n + k_val - 1) * (n + k_val))

# Since we want to clear denominators, we multiply the equation by the common denominator:
# Denominator of LHS: n * (n + 1 - k) * (n + k + 1) * (2*n + k - 1) * (2*n + k - 2)
# Let's do this directly with sympy.
LHS = alpha2 * ratio_np1 + alpha1 + alpha0 * ratio_nm1
RHS = ratio_kp1 * R_func(k + 1) - R_func(k)

diff = RHS - LHS
diff_simp = sp.simplify(diff)
print("Simplified difference numerator exists?")
# Let's get the numerator of diff_simp
num = sp.numer(diff_simp)
print("Numerator degree in n:", sp.degree(num, n))
print("Numerator degree in k:", sp.degree(num, k))

# Solve for coefficients to make the numerator identically 0
all_coeffs = list(coeffs.keys())
equations = []
for i in range(12):
    for j in range(12):
        coeff_val = num.coeff(n, i).coeff(k, j).subs(n, 0).subs(k, 0)
        if coeff_val != 0:
            equations.append(coeff_val)

print("Solving...")
sol = sp.solve(equations, all_coeffs)
print("Solution found?", len(sol) > 0)
if sol:
    print("S(n, k) =", S.subs(sol))
