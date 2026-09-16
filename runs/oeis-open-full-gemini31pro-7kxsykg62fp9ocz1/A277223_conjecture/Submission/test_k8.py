def S(m):
    return sum(int(c) for c in str(m))

for n in range(1, 100000):
    max_k = 0
    for k in range(1, 200):
        if S(k * n) == k:
            max_k = k
    if max_k < 12 and max_k not in [0, 9]:
        print(f"Counterexample!! n={n}, max_k={max_k}")
