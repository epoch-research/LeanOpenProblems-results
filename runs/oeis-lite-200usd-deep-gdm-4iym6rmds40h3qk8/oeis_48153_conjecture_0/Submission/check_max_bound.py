for n in range(5, 40):
    val_sum = 0
    for k in range(n):
        if 3 * k >= n + 1:
            val_sum += 3 * k - n - 1
    # We want 3 * val_sum >= (n-1)*(n-2)
    LHS = 3 * val_sum
    RHS = (n-1)*(n-2)
    diff = LHS - RHS
    print(f"n={n:2d} | LHS={LHS:3d} | RHS={RHS:3d} | diff={diff:3d}")
