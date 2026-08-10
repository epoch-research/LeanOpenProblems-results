def check():
    for n in range(5, 100):
        for k in range(n):
            lhs = 3 * (k**2 // n) + 2 * (n - k)
            rhs = k
            if lhs < rhs:
                print(f"FAILED for n={n}, k={k}")
                return
    print("ALL PASSED!")

check()
