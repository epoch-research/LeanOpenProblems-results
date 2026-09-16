def S(m):
    return sum(int(c) for c in str(m))

for n in range(19, 200000, 9):
    if S(n) == 10:
        valid = [k for k in range(11, 200) if S(k * n) == k]
        if not valid:
            print(f"No valid k > 10 up to 200 for n={n}")
