def S(m):
    return sum(int(c) for c in str(m))

n = 142857142858
print("n =", n)
print("S(7n) =", S(7 * n))
print("7n =", 7 * n)
for k in range(1, 100):
    if S(k * n) == k:
        print(f"k = {k} is valid")
