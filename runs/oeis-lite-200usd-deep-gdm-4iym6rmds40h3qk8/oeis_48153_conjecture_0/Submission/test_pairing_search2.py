def search():
    A = 2
    for B in range(-15, 5):
        failures = []
        for n in range(13, 100):
            for j in range(1, (n - 1) // 2 + 1):
                lhs = 6 * (j**2 // n) + 3 * n - 6 * j
                rhs = A * n + B
                if lhs < rhs:
                    failures.append((n, j, lhs, rhs))
        print(f"B={B:3d} | number of failures: {len(failures)}")
        if failures:
            print(f"  First failure: {failures[0]}")

search()
