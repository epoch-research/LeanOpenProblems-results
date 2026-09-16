import math

def min_fac(n):
    if n % 2 == 0: return 2
    if n % 3 == 0: return 3
    if n % 5 == 0: return 5
    if n % 7 == 0: return 7
    if n % 11 == 0: return 11
    if n % 13 == 0: return 13
    for i in range(17, int(math.isqrt(n)) + 1, 2):
        if n % i == 0: return i
    return n

c3 = []
for n in range(17, 6678672, 2):
    if n % 3 == 0 or n % 5 == 0 or n % 7 == 0 or n % 11 == 0 or n % 13 == 0: continue
    c = 0
    temp = n
    d = 17
    while d * d <= temp:
        while (temp % d) == 0:
            c += 1
            temp //= d
        d += 2
    if temp > 1:
        c += 1
    if c >= 3:
        c3.append(n)

print(len(c3))
with open("/workspace/leanproject/Submission/candidates.txt", "w") as f:
    for n in c3[:1000]:
        f.write(f"{n}\n")
