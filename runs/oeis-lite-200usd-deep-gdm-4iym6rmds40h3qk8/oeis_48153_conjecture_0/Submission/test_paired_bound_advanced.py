def check():
    for n in range(5, 100):
        # We check for all j <= n // 2
        # If j == n // 2: we only need >= n - 2
        # If j < n // 2: we check if >= 2 * (n - 2)
        for j in range(1, n // 2 + 1):
            lhs = 6 * (j**2 // n) + 3 * n - 6 * j
            if j == n // 2:
                rhs = n - 2
            else:
                rhs = 2 * (n - 2)
            if lhs < rhs:
                print(f"FAILED for n={n}, j={j}: lhs={lhs}, rhs={rhs}")
                return
    print("ALL PASSED!")

check()
