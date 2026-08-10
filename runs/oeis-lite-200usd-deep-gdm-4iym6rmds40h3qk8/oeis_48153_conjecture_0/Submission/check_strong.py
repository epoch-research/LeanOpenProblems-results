def actual_S_div(n):
    return sum(k**2 // n for k in range(n))

for n in range(6, 25):
    S_div = actual_S_div(n)
    LHS = 6 * S_div + n * n
    RHS = 3 * n * (n - 1) // 2
    diff = LHS - RHS
    print(f"n={n:2d} | LHS={LHS:3d} | RHS={RHS:3d} | diff={diff:3d}")
