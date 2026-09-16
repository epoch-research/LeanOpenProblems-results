import random

def S(m):
    return sum(int(c) for c in str(m))

def score(n):
    max_k = 0
    for k in range(11, 150):
        if S(k * n) == k:
            max_k = k
    return max_k

best = 999
for _ in range(100000):
    length = random.randint(5, 40)
    p = []
    rem = 10
    for i in range(10):
        if rem == 0: break
        d = random.randint(1, rem)
        p.append((random.randint(0, length), d))
        rem -= d
    n = 0
    for pos, d in p:
        n += d * 10**pos
    if S(n) != 10: continue
    s = score(n)
    if s == 0:
        s2 = 0
        for k in range(150, 1000):
            if S(k * n) == k:
                s2 = k
        if s2 == 0:
            print(f"FOUND! n={n}")
            exit(0)
        else:
            s = s2
    if s < best:
        best = s
        print(f"New best: {best} for n={n}")
