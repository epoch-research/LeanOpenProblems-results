import random

def S(m):
    return sum(int(c) for c in str(m))

partitions = []
def get_partitions(rem, max_val, current):
    if rem == 0:
        partitions.append(current)
        return
    for d in range(min(rem, max_val), 0, -1):
        get_partitions(rem - d, d, current + [d])
get_partitions(10, 9, [])

def check_partition(p):
    # p is a list of digits summing to 10
    # we randomly space them
    for _ in range(100):
        pos = [0]
        for _ in range(len(p)-1):
            pos.append(pos[-1] + random.randint(1, 10))
        n = sum(d * (10**pos[i]) for i, d in enumerate(p))
        
        max_k = 0
        for k in range(11, 200):
            if S(k * n) == k:
                max_k = k
                break
        if max_k == 0:
            return n
    return False

for p in partitions:
    res = check_partition(p)
    if res:
        print(f"Partition {p} gave counterexample {res}")
print("Done partitions")
