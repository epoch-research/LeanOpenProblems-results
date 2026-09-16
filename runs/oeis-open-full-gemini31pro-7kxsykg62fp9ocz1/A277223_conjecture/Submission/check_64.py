def S(m):
    return sum(int(c) for c in str(m))

n = 64
print([k for k in range(1, 200) if S(k * n) == k])
