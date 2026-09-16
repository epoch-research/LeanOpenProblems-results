for p in range(3, 100, 2):
    for q in range(p, 100, 2):
        P = p*q
        S = p+q
        M16 = (P+S-1)**2 - 4
        print(f"p={p}, q={q}, M16={M16}, P^2={P*P-1}, ratio={16*(P*P-1)/M16}")
