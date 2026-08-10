def choose(n, k):
    if k < 0 or k > n: return 0
    return binomial(n, k)

def a(n):
    if n == 0: return 1
    r = n - 1
    s = 0
    for k in range(n + 1):
        s += choose(n, k) * choose(2*n + k - 1, r)
    return s

m = 32
print("Precomputing b(n)...")
b = [QQ(a(m*i)) for i in range(3*m + 3)]
print("b(n) precomputed.")

# We set up the linear system for P and Q
# P has degree 2m (64). Coeffs c0..c64
# Q has degree 2m (64). Coeffs d0..d64. But Q is evaluated at n^2, so Q(n^2) = sum d_i n^(2i).
# We set d64 = 1.
# Total variables: c0..c64, d0..d63 (129 variables)

# We use 3m+1 (97) recurrence equations (n = 1..97) and m (32) symmetry equations
# This gives exactly 129 equations.
# Symmetry equations: P(k) = P(1-k) for k = 1..32

# Let's define the variables in Sage
ring = QQ['c0', 'c1', 'c2', 'c3', 'c4', 'c5', 'c6', 'c7', 'c8', 'c9', 'c10', 'c11', 'c12', 'c13', 'c14', 'c15', 'c16', 'c17', 'c18', 'c19', 'c20', 'c21', 'c22', 'c23', 'c24', 'c25', 'c26', 'c27', 'c28', 'c29', 'c30', 'c31', 'c32', 'c33', 'c34', 'c35', 'c36', 'c37', 'c38', 'c39', 'c40', 'c41', 'c42', 'c43', 'c44', 'c45', 'c46', 'c47', 'c48', 'c49', 'c50', 'c51', 'c52', 'c53', 'c54', 'c55', 'c56', 'c57', 'c58', 'c59', 'c60', 'c61', 'c62', 'c63', 'c64', 'd0', 'd1', 'd2', 'd3', 'd4', 'd5', 'd6', 'd7', 'd8', 'd9', 'd10', 'd11', 'd12', 'd13', 'd14', 'd15', 'd16', 'd17', 'd18', 'd19', 'd20', 'd21', 'd22', 'd23', 'd24', 'd25', 'd26', 'd27', 'd28', 'd29', 'd30', 'd31', 'd32', 'd33', 'd34', 'd35', 'd36', 'd37', 'd38', 'd39', 'd40', 'd41', 'd42', 'd43', 'd44', 'd45', 'd46', 'd47', 'd48', 'd49', 'd50', 'd51', 'd52', 'd53', 'd54', 'd55', 'd56', 'd57', 'd58', 'd59', 'd60', 'd61', 'd62', 'd63']
vars = list(ring.gens())

eqs = []
# Recurrence equations
for n in range(1, 3*m + 2):
    plus = prod(2*m*n + k for k in range(1, 2*m + 1))
    minus = prod(2*m*n - k for k in range(1, 2*m + 1))
    
    P_pos = sum(vars[i] * n**i for i in range(2*m + 1))
    P_neg = sum(vars[i] * (-n)**i for i in range(2*m + 1))
    
    # (-1)^32 = 1
    Q_val = sum(vars[2*m + 1 + i] * (n**2)**i for i in range(2*m)) + (n**2)**(2*m) # d64 = 1
    
    eq = plus * P_pos * b[n+1] + minus * P_neg * b[n-1] - Q_val * b[n]
    eqs.append(eq)

# Symmetry equations
for k in range(1, m + 1):
    eq = sum(vars[i] * k**i for i in range(2*m + 1)) - sum(vars[i] * (1 - k)**i for i in range(2*m + 1))
    eqs.append(eq)

print("Solving the linear system...")
# We solve the system of 129 equations in 129 variables
# Let's convert to a matrix form over QQ
A = matrix(QQ, 129, 129)
B = vector(QQ, 129)

for r_idx, eq in enumerate(eqs):
    # We want to extract coefficients of vars
    # eq is of the form LHS - Q_val_d64 * b[n]
    # Q_val_d64 has the term (n^2)^64 * b[n]
    # So the constant term of eq with respect to vars is the term from d64 = 1, which is - (n^2)^64 * b[n]
    # Wait, let's just extract the constant term and coefficients of vars directly in Sage
    for c_idx, v in enumerate(vars):
        A[r_idx, c_idx] = eq.coefficient(v)
    # The constant term is eq evaluated with all vars = 0
    B[r_idx] = -eq.subs({v: 0 for v in vars})

print("Solving matrix equation...")
sol = A.solve_right(B)
print("System solved!")

d_sol = [sol[2*m + 1 + i] for i in range(2*m)] + [1]
# Let's find roots of Q(y)
R_y = QQ['y']
Q_poly = sum(d_sol[i] * R_y.gen()**i for i in range(2*m + 1))

print("Finding roots of Q(y) using high precision...")
roots = Q_poly.roots(ring=CC)
print("Roots found:")
for r, mult in roots:
    if abs(r.imag()) < 1e-10:
        print(f"Real root: {r.real()}")
