def S(m):
    return sum(int(c) for c in str(m))

for n in range(19, 2000, 9):
    if S(n) == 10:
        valid = [k for k in range(1, 300) if S(k * n) == k]
        if max(valid) == 10:
            print(f"Counterexample! n={n}, max_k={max(valid)}")
