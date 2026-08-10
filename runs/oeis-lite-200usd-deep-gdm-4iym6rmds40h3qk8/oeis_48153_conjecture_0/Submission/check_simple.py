import math

def test_simple(n):
    m = (n - 1) // 2
    sum_paired = 0
    for j in range(1, m + 1):
        if 3 * j <= n + 1:
            term = 3 * n - 6 * j
        else:
            term = n - 2
        sum_paired += term
        
    j0_term = 0 # Wait, k=0 term has k^2/n = 0, so 3 * (0) = 0.
    
    if n % 2 == 0:
        mid_j = n // 2
        mid_term = 3 * (mid_j**2 // n)
        total_sum = sum_paired + j0_term + mid_term
    else:
        total_sum = sum_paired + j0_term
        
    # S_div sum is Sum_{k=0}^{n-1} (k^2 / n).
    # Since we pair j and n - j, we get:
    # S_div = (0^2 / n) + Sum_{j=1}^{m} ((n-j)^2/n + j^2/n) [+ (mid_j)^2/n if n is even]
    # Therefore:
    # 3 * S_div = 3 * (0) + Sum_{j=1}^{m} 3 * ((n-j)^2/n + j^2/n) [+ 3 * (mid_j^2/n) if n is even]
    # This matches total_sum!
    target = (n - 1) * (n - 2)
    diff = total_sum - target
    print(f"n={n:2d} | sum={total_sum:3d} | target={target:3d} | diff={diff:3d}")

for n in range(6, 40):
    test_simple(n)
