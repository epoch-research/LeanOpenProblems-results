def S(m):
    return sum(int(c) for c in str(m))
for n in range(1, 1000):
    if S(2*n) == 2 and S(18*n) != 18:
        print(f"n={n}, S(18n)={S(18*n)}, valid={ [k for k in range(1, 20) if S(k*n) == k] }")
