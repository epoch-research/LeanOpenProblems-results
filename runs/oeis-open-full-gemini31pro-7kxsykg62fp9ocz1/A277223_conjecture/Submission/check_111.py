def S(m):
    return sum(int(c) for c in str(m))

n = 1111111111
print("n =", n)
max_k = 0
valid = []
for k in range(1, 1000):
    if S(k * n) == k:
        valid.append(k)
        max_k = k
print("valid:", valid)
print("max_k:", max_k)
