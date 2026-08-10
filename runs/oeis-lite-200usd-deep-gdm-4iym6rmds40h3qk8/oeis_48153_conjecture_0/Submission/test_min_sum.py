def test_min_sum(n):
    tot = sum(min(n - 1, k * (n - k)) for k in range(n))
    target = n * (n - 1) // 2
    print(f"n={n:2d} | tot={tot:3d} | target={target:3d} | diff={target - tot:3d}")

for n in range(5, 20):
    test_min_sum(n)
