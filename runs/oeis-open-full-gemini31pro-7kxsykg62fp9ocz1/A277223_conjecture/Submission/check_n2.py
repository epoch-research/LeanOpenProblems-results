def S(m):
    return sum(int(c) for c in str(m))
valid = [k for k in range(1, 200) if S(k * 2) == k]
print(valid)
