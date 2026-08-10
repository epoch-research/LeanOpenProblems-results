def check():
    for n in range(13, 100):
        for j in range(1, (n - 1) // 2 + 1):
            lhs = 6 * (j**2 // n) + n + 4
            rhs = 6 * j
            if lhs < rhs:
                print(f"FAILED for n={n}, j={j}: lhs={lhs}, rhs={rhs}")
                return
    print("ALL PASSED!")

check()
