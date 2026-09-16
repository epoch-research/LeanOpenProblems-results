def S(m):
    return sum(int(c) for c in str(m))

for n in range(1, 200000, 9):
    if n == 1: continue
    max_k = 0
    for k in range(1, 100):
        if S(k * n) == k:
            max_k = k
    if max_k < 9:
        print(f"Counterexample! n={n}, max_k={max_k}")
