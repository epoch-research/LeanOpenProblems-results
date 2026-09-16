def S(m):
    return sum(int(c) for c in str(m))
print([k for k in range(1, 100) if S(k * 67) == k])
