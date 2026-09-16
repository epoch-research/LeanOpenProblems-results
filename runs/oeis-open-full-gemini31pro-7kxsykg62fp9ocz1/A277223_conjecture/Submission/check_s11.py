def S(m):
    return sum(int(c) for c in str(m))

for n in range(1, 100000):
    if S(n) == 11 and n % 11 == 0:
        n_div = n // 11
        max_k = 0
        for k in range(12, 500):
            if S(k * n_div) == k:
                max_k = k
        if max_k < 30:
            print(f"n_div={n_div}, n={n}, max_k={max_k}")
