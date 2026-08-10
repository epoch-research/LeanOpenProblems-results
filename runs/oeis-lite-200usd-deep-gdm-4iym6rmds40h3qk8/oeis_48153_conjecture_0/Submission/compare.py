def actual_S_div(n):
    return sum(k**2 // n for k in range(n))

def sum_piecewise_formula(n):
    m = (n - 1) // 2
    sum_paired = 0
    for j in range(1, m + 1):
        if j < n**0.5:
            term = 3 * n - 6 * j
        elif j <= n // 3:
            term = 3 * n - 6 * j + 6
        else:
            term = n - 2
        sum_paired += term
        
    j0_term = 3 * n
    
    if n % 2 == 0:
        mid_j = n // 2
        mid_term = 3 * (mid_j**2 // n)
        total_sum = sum_paired + j0_term + mid_term
    else:
        total_sum = sum_paired + j0_term
    return total_sum

for n in range(6, 15):
    act = 3 * actual_S_div(n)
    form = sum_piecewise_formula(n)
    print(f"n={n:2d} | actual={act:3d} | formula={form:3d} | diff={act-form:3d}")
