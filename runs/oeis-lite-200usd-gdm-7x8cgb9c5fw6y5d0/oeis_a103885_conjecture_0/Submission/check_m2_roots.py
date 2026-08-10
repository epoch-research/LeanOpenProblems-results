import sympy as sp

x = sp.Symbol('x')
y = sp.Symbol('y')

P = 110*x**4 - 220*x**3 + 148*x**2 - 38*x + 3
Q = 3463680*y**4 - 4551616*y**3 + 1696064*y**2 - 168064*y + 3456

# Check symmetry of P: P(x) = P(1-x)
P_sym = P.subs(x, 1-x)
print("P(1-x) == P(x):", sp.simplify(P - P_sym) == 0)

# Check roots of P
roots_P = sp.solve(P, x)
print("Roots of P:")
all_P_ok = True
for r in roots_P:
    r_val = r.evalf()
    is_real = sp.im(r_val) == 0
    in_interval = 0 <= r_val <= 1
    print(f"  {r} -> {r_val} (real: {is_real}, in [0,1]: {in_interval})")
    if not (is_real and in_interval):
        all_P_ok = False

# Check roots of Q(z^2) = 0
# The condition is: if Q(z^2) = 0, then z is real and z in [-1, 1].
# This is equivalent to: if Q(y) = 0, then y is real and y >= 0, and sqrt(y) in [0, 1], so y in [0, 1].
roots_Q = sp.solve(Q, y)
print("Roots of Q:")
all_Q_ok = True
for r in roots_Q:
    r_val = r.evalf()
    is_real = sp.im(r_val) == 0
    in_interval = 0 <= r_val <= 1
    print(f"  {r} -> {r_val} (real: {is_real}, in [0,1]: {in_interval})")
    if not (is_real and in_interval):
        all_Q_ok = False

print("All conditions satisfied for m=2:", all_P_ok and all_Q_ok)
