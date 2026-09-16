def S(m):
    return sum(int(c) for c in str(m))

n = 8 * 10**15 + 10**10 + 10**5 + 1
print(f"n={n}")
valid = []
for k in range(1, 3000):
    if S(k * n) == k:
        valid.append(k)
print(f"Valid multipliers: {valid}")
