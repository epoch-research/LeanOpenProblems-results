def S(m):
    return sum(int(c) for c in str(m))

fails = 0
for n in range(1, 100000):
    if S(n) == 10:
        if S(18 * n) != 18:
            fails += 1
            # print(f"n={n}, S(18n)={S(18*n)}")
print(f"Fails: {fails}")
