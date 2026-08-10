def check_ineq():
    for n in range(1, 100):
        ok = True
        for k in range((n + 1) // 2, n):
            lhs = 3 * (k**2 // n) + n
            rhs = 3 * k
            if lhs < rhs:
                ok = False
                break
        if ok:
            print(f"n={n} works!")

check_ineq()
