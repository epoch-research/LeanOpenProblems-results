def test_sum_sq_div_ge():
    for n in range(5, 25):
        S = sum(k**2 // n for k in range(n))
        # 3 * S + 2 * n^2 >= 2 * n * (n - 1)
        # So 3 * S >= 2 * n^2 - 2 * n - 2 * n^2 = -2 * n? No:
        # 2 * n * (n - 1) - 2 * n * n = 2 * n * n - 2 * n - 2 * n * n = -2 * n.
        # This is useless for a lower bound on S, because S is non-negative, and S >= -2 * n / 3 is always true.
        lhs = 3 * S + 2 * n * n
        rhs = 2 * n * (n - 1)
        print(f"n={n:2d} | lhs={lhs:4d} | rhs={rhs:4d} | diff={lhs - rhs:3d}")

test_sum_sq_div_ge()
