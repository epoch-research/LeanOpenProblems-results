import random

def S(m):
    return sum(int(c) for c in str(m))

for _ in range(100):
    pos = random.sample(range(50), 6)
    n = 5 * 10**pos[0] + sum(10**p for p in pos[1:])
    # check valid multipliers > 10
    max_k = 0
    for k in range(11, 200):
        if S(k * n) == k:
            max_k = k
    if max_k == 0:
        for k in range(200, 1000):
            if S(k * n) == k:
                max_k = k
        if max_k == 0:
            print(f"FOUND! n={n}")
            exit(0)
print("Not found")
