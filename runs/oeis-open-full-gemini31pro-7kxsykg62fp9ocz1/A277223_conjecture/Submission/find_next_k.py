def S(m):
    return sum(int(c) for c in str(m))

for K in [1, 2, 3, 4, 5, 6, 7, 8, 10, 11]:
    next_ks = set()
    first = True
    for n in range(1, 10000):
        if S(K*n) == K:
            valid = {k for k in range(K+1, 200) if S(k*n) == k}
            if first:
                next_ks = valid
                first = False
            else:
                next_ks = next_ks.intersection(valid)
    print(f"K={K}, intersection of next valid ks: {next_ks}")
