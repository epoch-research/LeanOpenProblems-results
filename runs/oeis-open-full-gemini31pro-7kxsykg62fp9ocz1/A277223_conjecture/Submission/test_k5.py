def S(m):
    return sum(int(c) for c in str(m))

for n in range(1, 10000):
    if n % 9 == 1:
        k = S(9 * n)
        if S(k * n) != k:
            print(f"Failed for n={n}: S(9n)={k}, S(k*n)={S(k*n)}")
