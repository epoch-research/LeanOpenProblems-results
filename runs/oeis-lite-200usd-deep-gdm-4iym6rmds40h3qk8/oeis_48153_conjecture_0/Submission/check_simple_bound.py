def actual_S_div(n):
    return sum(k**2 // n for k in range(n))

for n in range(5, 40):
    S_div = actual_S_div(n)
    LHS = 3 * S_div
    RHS = (n - 1) * (n - 2)
    diff = LHS - RHS
    print(f"n={n:2d} | LHS={LHS:3d} | RHS={RHS:3d} | diff={diff:3d}")
