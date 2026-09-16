import random
import time

def S(m):
    return sum(int(c) for c in str(m))

def score(n):
    # We want NO k > 10 to have S(k*n) == k
    # The score is the maximum k > 10 that satisfies S(k*n) == k
    # We want this max k to be 0 (meaning none exist)
    # Actually, we want to MINIMIZE the maximum valid k.
    # But it's binary for each k.
    max_k = 0
    for k in range(11, 200):
        if S(k * n) == k:
            max_k = k
    return max_k

# Start with a random n with S(n) = 10
def get_random_n(length):
    digits = [0]*length
    rem = 10
    for _ in range(10):
        idx = random.randint(0, length-1)
        digits[idx] += 1
    if digits[0] == 0:
        digits[0] = 1
        digits[random.randint(1, length-1)] -= 1
        # fix up if negative
        for i in range(1, length):
            if digits[i] < 0:
                digits[i] += 1
                digits[0] -= 1 # this might break sum, let's just do it simpler
    # simple generator
    s = ""
    for _ in range(length):
        if rem > 0:
            d = random.randint(0, min(9, rem))
        else:
            d = 0
        s += str(d)
        rem -= d
    if rem > 0:
        return get_random_n(length)
    if s[0] == '0':
        return get_random_n(length)
    return int(s)

best_n = None
best_score = 999999

for _ in range(10000):
    n = get_random_n(random.randint(10, 50))
    sc = score(n)
    if sc == 0:
        # Check larger k
        sc2 = 0
        for k in range(200, 1000):
            if S(k * n) == k:
                sc2 = k
        if sc2 == 0:
            print(f"FOUND! n={n}")
            exit(0)
        else:
            sc = sc2
    if sc < best_score:
        best_score = sc
        best_n = n
        print(f"New best: score={best_score} for n={best_n}")
