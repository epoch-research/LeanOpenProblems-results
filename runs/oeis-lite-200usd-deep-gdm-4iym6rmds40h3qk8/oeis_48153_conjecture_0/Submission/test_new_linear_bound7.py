def check():
    for n in range(5, 100):
        for k in range(n // 2, n):
            lhs = 3 * (k**2 // n) + n
            rhs = 3 * k - 1
            if lhs < rhs:
                print(f"FAILED for n={n}, k={k}: lhs={lhs}, rhs={rhs}")
                return
    print("ALL PASSED!")

check()
