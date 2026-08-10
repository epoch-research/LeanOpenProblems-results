def test_bounds_sum(n):
    m = n // 2
    part1 = sum(k * (n - 1) // 2 for k in range(m))
    part2 = sum((n - k) * (n - 1) // 2 for k in range(m, n))
    tot = part1 + part2
    target = n * (n - 1) // 2
    print(f"n={n:2d} | tot={tot:3d} | target={target:3d} | diff={target - tot:3d}")

for n in range(5, 20):
    test_bounds_sum(n)
