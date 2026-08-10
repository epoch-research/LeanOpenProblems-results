def A(n):
    return sum((k**2) % n for k in range(n))

for n in range(5, 25):
    val = A(n)
    target = (n**2 - 1) // 2
    all_min = sum(min(k**2, (n - k)**2, (k * (n - 1)) // 2, ((n - k) * (n - 1)) // 2, n - 1) for k in range(n))
    print(f"n={n:2d} | A(n)={val:3d} | target={target:3d} | all_min={all_min:3d} | diff={target - all_min:3d}")
