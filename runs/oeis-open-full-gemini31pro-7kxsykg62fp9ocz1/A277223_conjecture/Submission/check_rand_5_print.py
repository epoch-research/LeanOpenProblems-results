import random

def S(m):
    return sum(int(c) for c in str(m))

for _ in range(5):
    pos = random.sample(range(20), 6)
    n = 5 * 10**pos[0] + sum(10**p for p in pos[1:])
    valid = [k for k in range(11, 200) if S(k * n) == k]
    print(f"n={n}, valid={valid}")
