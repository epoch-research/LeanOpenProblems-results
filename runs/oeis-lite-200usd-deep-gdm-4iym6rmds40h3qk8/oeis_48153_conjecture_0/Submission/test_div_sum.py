for n in range(1, 40):
    lhs = sum((k**2) // n for k in range(n))
    rhs = (n - 1) * (n - 2) // 3
    diff = lhs - rhs
    print(f"n={n:2d} | lhs={lhs:3d} | rhs={rhs:3d} | diff={diff:3d}")
