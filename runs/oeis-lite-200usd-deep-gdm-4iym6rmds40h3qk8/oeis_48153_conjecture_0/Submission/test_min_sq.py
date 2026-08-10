def A(n):
    return sum((k**2) % n for k in range(n))

for n in range(5, 25):
    val = A(n)
    target = (n**2 - 1) // 2
    min_sq = sum(min(k**2, (n - k)**2, n - 1) for k in range(n))
    print(f"n={n:2d} | A(n)={val:3d} | target={target:3d} | min_sq={min_sq:3d} | diff={target - min_sq:3d}")
