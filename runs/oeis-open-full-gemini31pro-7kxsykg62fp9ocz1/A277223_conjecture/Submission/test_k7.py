def S(m):
    return sum(int(c) for c in str(m))

for n in [64, 73, 271, 316]:
    valid = [k for k in range(1, 2000) if S(k * n) == k]
    print(f"n={n}, max valid: {max(valid) if valid else 0}")
