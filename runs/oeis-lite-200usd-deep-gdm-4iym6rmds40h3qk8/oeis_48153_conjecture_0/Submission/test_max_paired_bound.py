def check():
    for n in range(5, 100):
        m = (n - 1) // 2
        sum_val = 0
        for j in range(1, m + 1):
            val1 = 3 * n - 6 * j
            val2 = 2 * n - 4 * j + 2
            sum_val += max(val1, val2)
        
        # If even, add middle term
        if n % 2 == 0:
            sum_val += 3 * ( (n // 2) // 2 )  # 3 * (m/2) is 3 * (n/4)
        
        target = (n - 1) * (n - 2)
        if sum_val < target:
            print(f"FAILED for n={n}: sum={sum_val}, target={target}")
            return
    print("ALL PASSED!")

check()
