def check():
    for n in range(5, 100):
        sum_val = 0
        for k in range(n):
            b1 = k * (n - 1) // 2
            b2 = (n - k) * (n - 1) // 2
            sum_val += min(b1, b2)
        target = n * (n - 1) // 2
        print(f"n={n:2d} | sum={sum_val:3d} | target={target:3d} | diff={sum_val - target:3d}")

check()
