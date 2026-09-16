def S(m):
    return sum(int(c) for c in str(m))

fails = 0
for n in range(1, 10000):
    for K in range(1, 9):
        if S(K*n) == K:
            if S(9*n) != 9:
                fails += 1
                # print(f"n={n}, K={K}, S(9n)={S(9*n)}")
print(f"Total fails: {fails}")
