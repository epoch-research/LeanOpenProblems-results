def test_linear_combination(n):
    # We want to find A, B, C such that sum(A * (k**2 // n) + B * k + C) is related to (n-1)*(n-2)
    # Actually, we know 3 * sum(k**2 // n) is at least (n-1)*(n-2)
    S = sum(k**2 // n for k in range(n))
    target = (n-1)*(n-2)
    print(f"n={n:2d} | 3*S={3*S:3d} | target={target:3d} | diff={3*S - target:3d}")

for n in range(5, 15):
    test_linear_combination(n)
