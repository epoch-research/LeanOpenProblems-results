def S(m):
    return sum(int(c) for c in str(m))

n = 9991 * 10**21
print("n =", n)
print("S(7n) =", S(7 * n))
for k in range(8, 500):
    if S(k * n) == k:
        print(f"valid k={k}")
