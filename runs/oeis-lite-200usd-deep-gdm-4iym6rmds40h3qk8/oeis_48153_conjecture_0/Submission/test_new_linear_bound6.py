def check():
    for n in range(6, 100):
        for k in range(n // 2, n):
            lhs = 3 * (k**2 // n) + n + 2
            rhs = 3 * k
            if lhs < rhs:
                print(f"FAILED for n={n}, k={k}")
                return
    print("ALL PASSED!")

check()
