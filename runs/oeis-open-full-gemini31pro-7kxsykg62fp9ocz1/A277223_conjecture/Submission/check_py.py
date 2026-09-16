def S(m):
    return sum(int(c) for c in str(m))

n = 1428571428571428571428571428571428715
print("S(7n) =", S(7 * n))
valid = []
for k in range(1, 1500):
    if S(k * n) == k:
        valid.append(k)
print("Valid k up to 1500:", valid)
