for p in range(3, 1000, 2):
    for q in range(p, 1000, 2):
        P = p*q
        S = p+q
        M16 = (P+S-1)**2 - 4
        if (16*(P*P-1)) % M16 == 0:
            print(f"p={p}, q={q}, ratio={16*(P*P-1)//M16}")
