def S(m):
    return sum(int(c) for c in str(m))

def check_partition(p):
    # p is a list of digits
    for k in range(11, 2000):
        s = sum(S(k * d) for d in p)
        if s == k:
            return k
    return 0

def gen_partitions(rem, max_val, current):
    if rem == 0:
        k = check_partition(current)
        if k == 0:
            print(f"FOUND COUNTEREXAMPLE PARTITION: {current}")
        return
    for d in range(min(rem, max_val), 0, -1):
        gen_partitions(rem - d, d, current + [d])

gen_partitions(10, 9, [])
gen_partitions(11, 9, [])
gen_partitions(7, 7, [])
gen_partitions(8, 8, [])
print("Done")
