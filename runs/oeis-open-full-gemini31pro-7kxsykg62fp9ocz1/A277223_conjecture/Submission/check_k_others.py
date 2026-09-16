def S(m):
    return sum(int(c) for c in str(m))

for target in [7, 8, 10, 11]:
    for n in range(1, 20000):
        if S(target*n) == target:
            valid = [k for k in range(target+1, 200) if S(k*n) == k]
            if not valid or max(valid) < 9:
                # wait, if target=10, max(valid) < 9 is always false if valid is not empty
                pass
            if not valid and target in [7, 8, 10, 11]:
                print(f"target={target}, n={n}, no larger valid")
