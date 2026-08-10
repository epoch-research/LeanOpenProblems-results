def test_sum_paired(n):
    m = (n - 1) // 2
    # Sum of paired bounds for j = 1..m
    sum_paired = sum(2 * n - 4 * j + 2 for j in range(1, m + 1))
    
    # j = 0 term: 3 * (0^2 / n + n^2 / n) = 3 * n
    j0_term = 3 * n
    
    # If n is even, we have a middle term j = n//2
    # Its contribution to the sum 3 * S_div is:
    # 3 * ( (n//2)^2 / n )
    if n % 2 == 0:
        mid_j = n // 2
        mid_term = 3 * (mid_j**2 // n)
        total_sum = sum_paired + j0_term + mid_term
    else:
        total_sum = sum_paired + j0_term
        
    target = (n - 1) * (n - 2)
    print(f"n={n:2d} | sum={total_sum:3d} | target={target:3d} | diff={total_sum - target:3d}")

for n in range(6, 25):
    test_sum_paired(n)
