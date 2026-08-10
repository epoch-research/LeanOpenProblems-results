def check():
    for n in range(13, 100):
        for k in range(n):
            lhs = 3 * (k**2 // n) + n + 4
            rhs = 3 * k
            if lhs < rhs:
                print(f"FAILED for n={n}, k={k}")
                return
    print("ALL PASSED!")

check()
