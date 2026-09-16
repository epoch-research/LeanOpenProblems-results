def S(m):
    return sum(int(c) for c in str(m))

def check_partition(p, target):
    for k in range(target + 1, 3000):
        if k == 9: continue
        s = sum(S(k * d) for d in p)
        if s == k:
            return k
    return 0

def gen_partitions(target):
    def gen(rem, max_val, current):
        if rem == 0:
            k = check_partition(current, target)
            if k == 0:
                print(f"Target {target}, COUNTEREXAMPLE PARTITION: {current}")
            return
        for d in range(min(rem, max_val), 0, -1):
            gen(rem - d, d, current + [d])
    gen(target, 9, [])

for t in [7, 8, 10, 11]:
    gen_partitions(t)
print("Done")
