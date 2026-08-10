def check():
    for n in range(13, 100):
        # Odd case: m = (n-1)//2 terms of 2*(n-2)
        # Even case: m-1 terms of 2*(n-2), 1 term of n-2
        m = (n - 1) // 2
        if n % 2 == 1:
            total_sum = m * 2 * (n - 2)
        else:
            total_sum = (m - 1) * 2 * (n - 2) + (n - 2)
            
        # Add the j=0 term: 3 * (0^2 / n + n^2 / n) = 3 * n
        # Wait, S_div = 0^2/n + sum_{j=1}^{m} ( j^2/n + (n-j)^2/n ) (+ mid if even)
        # So 3 * S_div = 3 * (0) + sum_{j=1}^{m} 3 * ( j^2/n + (n-j)^2/n ) (+ mid if even)
        # So the sum of paired bounds is exactly 3 * S_div!
        # Because we pair k and n-k for k = 1..m.
        # k=0 is just 3 * (0^2/n) = 0.
        # So 3 * S_div is exactly the sum of paired terms!
        
        target = (n - 1) * (n - 2)
        print(f"n={n:2d} | sum={total_sum:3d} | target={target:3d} | diff={total_sum - target:3d}")

check()
