import random

def S(m):
    return sum(int(c) for c in str(m))

for _ in range(20000):
    pos = random.sample(range(1000), 10)
    n = sum(10**p for p in pos)
    # Check if a(n) == 10
    max_k = 10
    for k in range(11, 200):
        if S(k * n) == k:
            max_k = k
            break
    if max_k == 10:
        for k in range(200, 1000):
            if S(k * n) == k:
                max_k = k
                break
        if max_k == 10:
            print(f"FOUND! n={n}")
            exit(0)
print("Not found")
