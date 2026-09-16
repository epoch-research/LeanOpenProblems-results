import random

def S(m):
    return sum(int(c) for c in str(m))

def check(p):
    val = sum(10**x for x in p)
    if val % 11 != 0:
        return False
    n = val // 11
    max_k = 0
    for k in range(12, 100):
        if S(k * n) == k:
            max_k = k
            break
    if max_k == 0:
        for k in range(100, 200):
            if S(k * n) == k:
                max_k = k
                break
        if max_k == 0:
            return n
    return False

for _ in range(100000):
    p = [random.randint(0, 100) for _ in range(11)]
    res = check(p)
    if res:
        print(f"FOUND: n={res}")
        exit(0)
print("Not found in 100000 random samples.")
