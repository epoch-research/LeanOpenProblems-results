def inv(j, p):
    return pow(j, p-2, p)
for p in [3, 5, 7, 11, 13]:
    s = sum((-1)**j * inv(j, p) for j in range(1, p)) % p
    for k in range(p):
        if (pow(2, p-1, p**2) - 1)//p % p == (k * s) % p:
            print(p, "k =", k)
