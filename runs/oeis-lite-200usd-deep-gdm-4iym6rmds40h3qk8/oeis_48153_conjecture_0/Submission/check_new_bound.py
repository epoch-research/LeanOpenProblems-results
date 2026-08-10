def check():
    for n in range(12, 100):
        m = (n - 1) // 2
        sum_paired = 0
        for j in range(1, m + 1):
            if 3 * j <= n + 1:
                term = 3 * n - 6 * j
            else:
                term = n + 2
            sum_paired += term
        
        j0_term = 0
        
        if n % 2 == 0:
            mid_j = n // 2
            mid_term = 3 * (mid_j**2 // n)
            total_sum = sum_paired + j0_term + mid_term
        else:
            total_sum = sum_paired + j0_term
            
        target = (n - 1) * (n - 2)
        print(f"n={n:2d} | sum={total_sum:3d} | target={target:3d} | diff={total_sum - target:3d}")

check()
