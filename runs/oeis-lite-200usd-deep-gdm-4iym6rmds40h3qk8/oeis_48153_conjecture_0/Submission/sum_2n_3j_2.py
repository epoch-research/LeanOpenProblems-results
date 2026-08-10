def check():
    for n in range(11, 100):
        m = (n - 1) // 2
        sum_val = sum(2 * n - 3 * j + 2 for j in range(1, m + 1))
        
        # If even, add middle term j = n//2
        if n % 2 == 0:
            mid_j = n // 2
            sum_val += 3 * (mid_j**2 // n)
            
        target = (n - 1) * (n - 2)
        print(f"n={n:2d} | sum={sum_val:3d} | target={target:3d} | diff={sum_val - target:3d}")

check()
