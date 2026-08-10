def check():
    for n in range(5, 100):
        # We only check for j < (n + 1) // 2
        # Since if n is even, j < n/2 means j <= n/2 - 1.
        # If n is odd, j <= (n-1)/2.
        m = (n - 1) // 2
        for j in range(1, m + 1):
            lhs = 6 * (j**2 // n) + 3 * n - 6 * j
            rhs = 2 * n - 4 * j + 2
            if lhs < rhs:
                print(f"FAILED for n={n}, j={j}: lhs={lhs}, rhs={rhs}")
                return
    print("ALL PASSED!")

check()
