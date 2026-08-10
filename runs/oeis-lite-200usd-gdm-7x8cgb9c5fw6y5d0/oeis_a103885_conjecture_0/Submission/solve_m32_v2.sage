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
b = [QQ(a(m*i)) for i in range(3*m + 3)]

ring = QQ['c0', 'c1', 'c2', 'c3', 'c4', 'c5', 'c6', 'c7', 'c8', 'c9', 'c10', 'c11', 'c12', 'c13', 'c14', 'c15', 'c16', 'c17', 'c18', 'c19', 'c20', 'c21', 'c22', 'c23', 'c24', 'c25', 'c26', 'c27', 'c28', 'c29', 'c30', 'c31', 'c32', 'c33', 'c34', 'c35', 'c36', 'c37', 'c38', 'c39', 'c40', 'c41', 'c42', 'c43', 'c44', 'c45', 'c46', 'c47', 'c48', 'c49', 'c50', 'c51', 'c52', 'c53', 'c54', 'c55', 'c56', 'c57', 'c58', 'c59', 'c60', 'c61', 'c62', 'c63', 'c64', 'd0', 'd1', 'd2', 'd3', 'd4', 'd5', 'd6', 'd7', 'd8', 'd9', 'd10', 'd11', 'd12', 'd13', 'd14', 'd15', 'd16', 'd17', 'd18', 'd19', 'd20', 'd21', 'd22', 'd23', 'd24', 'd25', 'd26', 'd27', 'd28', 'd29', 'd30', 'd31', 'd32', 'd33', 'd34', 'd35', 'd36', 'd37', 'd38', 'd39', 'd40', 'd41', 'd42', 'd43', 'd44', 'd45', 'd46', 'd47', 'd48', 'd49', 'd50', 'd51', 'd52', 'd53', 'd54', 'd55', 'd56', 'd57', 'd58', 'd59', 'd60', 'd61', 'd62', 'd63']
vars = list(ring.gens())

eqs = []
for n in range(1, 3*m + 2):
    plus = prod(2*m*n + k for k in range(1, 2*m + 1))
    minus = prod(2*m*n - k for k in range(1, 2*m + 1))
    P_pos = sum(vars[i] * n**i for i in range(2*m + 1))
    P_neg = sum(vars[i] * (-n)**i for i in range(2*m + 1))
    Q_val = sum(vars[2*m + 1 + i] * (n**2)**i for i in range(2*m)) + (n**2)**(2*m)
    eq = plus * P_pos * b[n+1] + minus * P_neg * b[n-1] - Q_val * b[n]
    eqs.append(eq)

for k in range(1, m + 1):
    eq = sum(vars[i] * k**i for i in range(2*m + 1)) - sum(vars[i] * (1 - k)**i for i in range(2*m + 1))
    eqs.append(eq)

A = matrix(QQ, 129, 129)
B = vector(QQ, 129)
for r_idx, eq in enumerate(eqs):
    for c_idx, v in enumerate(vars):
        A[r_idx, c_idx] = eq.coefficient(v)
    B[r_idx] = -eq.subs({v: 0 for v in vars})

sol = A.solve_right(B)
d_sol = [sol[2*m + 1 + i] for i in range(2*m)] + [1]
R_y = QQ['y']
Q_poly = sum(d_sol[i] * R_y.gen()**i for i in range(2*m + 1))

# Check sign changes at negative values
for y_val in range(-30, 0):
    val = Q_poly(y_val)
    print(f"Q({y_val}) sign: {sign(val)} (value: {float(val)})")
