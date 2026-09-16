def S(m):
    return sum(int(c) for c in str(m))

for n in range(1, 100000):
    max_k = 0
    for k in range(1, 150):
        if S(k * n) == k:
            max_k = k
    if max_k < 9:
        print(f"Counterexample to a(n) >= 9: n={n}, max_k={max_k}")
