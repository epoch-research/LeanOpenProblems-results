def A(n):
    return sum((k**2) % n for k in range(n))

def UB(n):
    ub1 = sum(k * (n - 1) // 2 for k in range(n // 2))
    ub2 = sum((n - k) * (n - 1) // 2 for k in range(n // 2, n))
    return ub1 + ub2

for n in range(5, 50):
    ub = UB(n)
    target = n * (n - 1) // 2
    print(f"n={n:2d} | UB(n)={ub:4d} | target={target:4d} | diff={target - ub:4d}")
