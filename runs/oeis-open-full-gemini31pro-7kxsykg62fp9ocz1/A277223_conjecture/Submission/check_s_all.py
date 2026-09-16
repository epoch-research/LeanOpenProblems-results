def S(m):
    return sum(int(c) for c in str(m))

def gen_partitions(n, max_val, length):
    if length == 0:
        if n == 0:
            yield []
        return
    for i in range(min(n, max_val), -1, -1):
        for p in gen_partitions(n - i, max_val, length - 1):
            yield [i] + p

def check():
    for target in [7, 8, 10, 11]:
        for length in range(1, 12):
            for p in gen_partitions(target, 9, length):
                if p[0] == 0:
                    continue
                n = int("".join(map(str, p)))
                max_k = 0
                for k in range(1, 150):
                    if S(k * n) == k:
                        max_k = k
                if max_k == target:
                    print(f"Counterexample! n = {n}, max_k = {target}")
                    return
check()
print("Done")
