def check():
    for C in range(1, 10):
        ok = True
        for n in range(5, 100):
            for k in range(n):
                lhs = 3 * (k**2 // n) + 2 * (n - k) + C
                rhs = 3 * k
                if lhs < rhs:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            print(f"FOUND: C={C}")
            return

check()
