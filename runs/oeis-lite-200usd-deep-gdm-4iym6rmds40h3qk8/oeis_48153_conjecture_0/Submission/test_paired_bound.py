def check():
    for n in range(5, 100):
        for j in range(1, n // 2 + 1):
            lhs = 6 * (j**2 // n) + 3 * n - 6 * j
            rhs = n - 2
            if lhs < rhs:
                print(f"FAILED for n={n}, j={j}: lhs={lhs}, rhs={rhs}")
                return
    print("ALL PASSED!")

check()
