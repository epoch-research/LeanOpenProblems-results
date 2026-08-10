def A(n):
    return sum((k**2) % n for k in range(n))

for n in range(5, 20):
    val = A(n)
    target = (n**2 - 1) // 2
    
    # sum of min bounds
    min_bound = sum(min((k * (n - 1)) // 2, ((n - k) * (n - 1)) // 2) for k in range(n))
    
    print(f"n={n:2d} | A(n)={val:3d} | target={target:3d} | min_bound={min_bound:3d}")
