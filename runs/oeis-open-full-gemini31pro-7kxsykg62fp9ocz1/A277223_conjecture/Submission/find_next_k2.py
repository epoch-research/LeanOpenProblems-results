def S(m):
    return sum(int(c) for c in str(m))

print("For K=5:")
for n in range(1, 10000):
    if S(5*n) == 5:
        valid = {k for k in range(6, 200) if S(k*n) == k}
        print(f"n={n}, 5n={5*n}, next={sorted(list(valid))[:5]}")
