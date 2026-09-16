for p in [3, 5, 7, 11, 13]:
    s = sum((-1)**j * pow(j, p-2, p**2) for j in range(1, p))
    fq = (pow(2, p-1) - 1) // p
    print(p, s % p, fq % p)
