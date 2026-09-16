for p in range(3, 1000, 2):
    for q in range(p, 1000, 2):
        P = p * q
        S = p + q
        M = (P + S + 1) // 4 * ((P + S - 3) // 4)
        if M > 0 and (P**2 - 1) % M == 0:
            print(f"Match: {p}, {q}")
