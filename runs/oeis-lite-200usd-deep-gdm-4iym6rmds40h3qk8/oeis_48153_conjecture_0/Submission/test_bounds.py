def A(n):
    return sum((k**2) % n for k in range(n))

for n in range(5, 20):
    val = A(n)
    target = (n**2 - 1) // 2
    # split at n // 2
    m = n // 2
    b1_half = sum((k * (n - 1)) // 2 for k in range(m))
    b2_half = sum(((n - k) * (n - 1)) // 2 for k in range(m, n))
    bound_half = b1_half + b2_half
    
    # split at (n + 1) // 2
    m2 = (n + 1) // 2
    b1_half2 = sum((k * (n - 1)) // 2 for k in range(m2))
    b2_half2 = sum(((n - k) * (n - 1)) // 2 for k in range(m2, n))
    bound_half2 = b1_half2 + b2_half2
    
    print(f"n={n:2d} | A(n)={val:3d} | target={target:3d} | bound_n/2={bound_half:3d} | bound_(n+1)/2={bound_half2:3d}")
