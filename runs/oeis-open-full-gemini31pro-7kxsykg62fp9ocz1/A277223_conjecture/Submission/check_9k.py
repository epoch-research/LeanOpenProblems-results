def S(m):
    return sum(int(c) for c in str(m))

for K in [1,2,3,4,5,6,7,8,10,11]:
    fails = 0
    for n in range(1, 1000):
        if S(K*n) == K:
            if S(9*K*n) != 9*K:
                fails += 1
    print(f"K={K}, fails={fails}")
