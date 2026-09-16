def S(m):
    return sum(int(c) for c in str(m))

for n in range(1, 100000):
    if S(n) == 10:
        max_k = 0
        for k in range(11, 500):
            if S(k * n) == k:
                max_k = k
        print(f"n={n}, max_k={max_k}")
