def A(n):
    return sum((k**2) % n for k in range(n))

for n in range(1, 40):
    val = A(n)
    target = n * (n - 1) // 2
    diff = target - val
    print(f"n={n:2d} | A(n)={val:3d} | target={target:3d} | diff={diff:3d}")
