def check():
    for C in range(1, 10):
        for n0 in range(5, 30):
            ok = True
            for n in range(n0, 100):
                for k in range(n):
                    lhs = 3 * (k**2 // n) + n + C
                    rhs = 4 * k
                    if lhs < rhs:
                        ok = False
                        break
                if not ok:
                    break
            if ok:
                print(f"FOUND: C={C}, n0={n0}")
                return

check()
