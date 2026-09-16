def S(m):
    return sum(int(c) for c in str(m))

def get_partitions(rem, max_val, current):
    if rem == 0:
        if any(d >= 5 for d in current):
            yield current
        return
    for d in range(min(rem, max_val), 0, -1):
        yield from get_partitions(rem - d, d, current + [d])

def check_config(p, gaps):
    n = 0
    pos = 0
    for i, d in enumerate(p):
        n += d * 10**pos
        if i < len(gaps):
            pos += gaps[i]
    
    # check valid k
    max_k = 0
    for k in range(11, 200):
        if S(k * n) == k:
            max_k = k
    return max_k

import itertools
for p in get_partitions(10, 9, []):
    num_gaps = len(p) - 1
    # gaps can be from 1 to 4
    for gaps in itertools.product(range(1, 5), repeat=num_gaps):
        n = 0
        pos = 0
        for i, d in enumerate(p):
            n += d * 10**pos
            if i < num_gaps:
                pos += gaps[i]
        
        # We need S(kn) != k for all k >= 11.
        # Let's find the max_k
        max_k = 0
        for k in range(11, 200):
            if S(k * n) == k:
                max_k = k
        if max_k == 0:
            print(f"FOUND! p={p}, gaps={gaps}, n={n}")
print("Done")
