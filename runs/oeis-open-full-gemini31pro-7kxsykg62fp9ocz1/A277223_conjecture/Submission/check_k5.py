def S(m):
    return sum(int(c) for c in str(m))

for n in range(1, 10000):
    if S(5*n) == 5:
        valid = [k for k in range(6, 200) if S(k*n) == k]
        if not valid or max(valid) < 9:
            print(f"n={n}, valid={valid}")
