import random

def S(m):
    return sum(int(c) for c in str(m))

for _ in range(10):
    pos = random.sample(range(100), 10)
    n = sum(10**p for p in pos)
    print(f"n={n}")
    for k in range(11, 30):
        print(f"k={k}, S={S(k*n)}")
