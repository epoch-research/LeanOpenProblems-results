def S(m):
    return sum(int(c) for c in str(m))

for n in range(1, 10000):
    for K in range(1, 9):
        if S(K*n) == K:
            if S(9*n) != 9:
                valid = [k for k in range(1, 200) if S(k*n) == k]
                if max(valid) < 12:
                    print(f"n={n}, K={K}, S(9n)={S(9*n)}, valid={valid}")
