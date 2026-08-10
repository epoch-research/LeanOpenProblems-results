def choose(n, k):
    import math
    return math.comb(n, k)

p = 5
print(f"p = {p}")
total = 0
for k in range(2 * p + 1):
    t1 = choose(p + k - 1, k)
    t2 = t1**2
    term = 3 * t2 + 4 * t1
    total += term
    print(f"k = {k:2d}: t1 = {t1:5d}, t2 = {t2:8d}, 3*t2 + 4*t1 = {term:8d}, mod p^5 = {term % (p**5):5d}")

print(f"Total = {total}, mod p^5 = {total % (p**5)}")
