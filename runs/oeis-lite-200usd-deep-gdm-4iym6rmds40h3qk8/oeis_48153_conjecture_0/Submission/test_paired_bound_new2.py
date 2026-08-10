def check():
    for n in range(6, 100):
        m = (n - 1) // 2
        for j in range(1, m + 1):
            lhs = 6 * (j**2 // n) + 3 * n - 6 * j
            rhs = 2 * n - 4 * j + 2
            if lhs < rhs:
                print(f"FAILED for n={n}, j={j}: lhs={lhs}, rhs={rhs}")
                return
    print("ALL PASSED FOR n >= 6!")

check()
