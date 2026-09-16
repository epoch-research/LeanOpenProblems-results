def S(m):
    return sum(int(c) for c in str(m))

for n in [64, 73, 271, 316]:
    valid = [k for k in range(1, 200) if S(k * n) == k]
    print(f"n={n}, valid multipliers: {valid}")
