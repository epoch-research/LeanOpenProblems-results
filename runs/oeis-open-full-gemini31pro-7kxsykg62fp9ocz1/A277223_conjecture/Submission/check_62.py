def S(m):
    return sum(int(c) for c in str(m))
n = 62
valid = [k for k in range(1, 1000) if S(k * n) == k]
print(valid)
