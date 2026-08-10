def check():
    for n in range(5, 100):
        for k in range(n):
            lhs = 3 * (k**2 // n) + n
            rhs = 3 * k - 2
            if lhs < rhs:
                print(f"FAILED for n={n}, k={k}")
                return
    print("ALL PASSED!")

check()
