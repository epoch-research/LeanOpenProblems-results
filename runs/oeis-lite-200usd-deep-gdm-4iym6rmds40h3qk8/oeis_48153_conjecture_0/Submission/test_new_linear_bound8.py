def check():
    for n in range(5, 100):
        for k in range(n):
            lhs = 6 * (k**2 // n) + 2 * n
            rhs = 5 * k - 2
            if lhs < rhs:
                print(f"FAILED for n={n}, k={k}: lhs={lhs}, rhs={rhs}")
                return
    print("ALL PASSED!")

check()
