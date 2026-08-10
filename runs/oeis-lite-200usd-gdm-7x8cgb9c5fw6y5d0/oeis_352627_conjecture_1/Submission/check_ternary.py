def check_ternary(limit):
    represented = set()
    for a in range(int(limit**0.5) + 1):
        for b in range(int((limit/2.0)**0.5) + 1):
            for c in range(int(limit**0.5) + 1):
                val = a**2 + 2*(b**2) + c**2
                if val < limit:
                    represented.add(val)
    for n in range(limit):
        if n not in represented:
            print(f"Not represented: {n}")
            return
    print("All represented!")

check_ternary(100)
