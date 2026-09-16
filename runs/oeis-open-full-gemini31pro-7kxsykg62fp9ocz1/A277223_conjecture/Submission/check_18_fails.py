def S(m):
    return sum(int(c) for c in str(m))

for n in range(1, 10000):
    if S(n) == 10:
        if S(18 * n) != 18:
            valid = [k for k in range(11, 200) if S(k*n) == k]
            print(f"n={n}, S(18n)={S(18*n)}, valid={valid[:3]}")
