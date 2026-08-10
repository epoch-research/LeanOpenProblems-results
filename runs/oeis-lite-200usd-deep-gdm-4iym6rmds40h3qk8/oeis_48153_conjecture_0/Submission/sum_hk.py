def test_sum_hk(n):
    sum_hk = 0
    for k in range(n):
        if 3 * k <= n + 1:
            val = 0
        else:
            val = 3 * k - n - 1
        sum_hk += val
    target = (n - 1) * (n - 2)
    print(f"n={n:2d} | sum_hk={sum_hk:3d} | target={target:3d} | diff={sum_hk - target:3d}")

for n in range(5, 25):
    test_sum_hk(n)
