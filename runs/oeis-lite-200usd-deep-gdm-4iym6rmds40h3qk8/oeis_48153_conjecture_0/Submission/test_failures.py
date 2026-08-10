def check():
    C = 2
    failures = []
    for n in range(5, 100):
        for k in range(n):
            lhs = 3 * (k**2 // n) + 2 * (n - k) + C
            rhs = 3 * k
            if lhs < rhs:
                failures.append((n, k, lhs, rhs))
    print(f"Number of failures for C={C}: {len(failures)}")
    if failures:
        print(f"  First failure: {failures[0]}")
        print(f"  Last failure: {failures[-1]}")

check()
