def S(m):
    return sum(int(c) for c in str(m))

for n in range(1, 40000):
    for K in [10, 11]:
        if S(K*n) == K:
            valid = [k for k in range(K+1, 200) if S(k*n) == k]
            if not valid:
                print(f"Counterexample! n={n}, K={K}")
