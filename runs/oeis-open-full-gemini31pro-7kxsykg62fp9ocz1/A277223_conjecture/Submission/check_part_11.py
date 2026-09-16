def S(m):
    return sum(int(c) for c in str(m))

def check_partition(p):
    # check k=11
    s11 = sum(S(11 * d) for d in p)
    if s11 != 11:
        return False
    # check k >= 12
    for k in range(12, 3000):
        sk = sum(S(k * d) for d in p)
        if sk == k:
            return False
    return True

def gen_partitions(rem, max_val, current):
    if rem == 0:
        if check_partition(current):
            print(f"FOUND COUNTEREXAMPLE PARTITION FOR 11: {current}")
        return
    for d in range(min(rem, max_val), 0, -1):
        gen_partitions(rem - d, d, current + [d])

print("Checking 11...")
gen_partitions(11, 9, [])
print("Checking 10...")
def check_partition_10(p):
    s10 = sum(S(10 * d) for d in p)
    if s10 != 10: return False
    for k in range(11, 3000):
        sk = sum(S(k * d) for d in p)
        if sk == k: return False
    return True

def gen_partitions_10(rem, max_val, current):
    if rem == 0:
        if check_partition_10(current):
            print(f"FOUND COUNTEREXAMPLE PARTITION FOR 10: {current}")
        return
    for d in range(min(rem, max_val), 0, -1):
        gen_partitions_10(rem - d, d, current + [d])
gen_partitions_10(10, 9, [])

print("Checking 8...")
def check_partition_8(p):
    s8 = sum(S(8 * d) for d in p)
    if s8 != 8: return False
    for k in range(9, 3000):
        if k == 9: continue
        sk = sum(S(k * d) for d in p)
        if sk == k: return False
    return True

def gen_partitions_8(rem, max_val, current):
    if rem == 0:
        if check_partition_8(current):
            print(f"FOUND COUNTEREXAMPLE PARTITION FOR 8: {current}")
        return
    for d in range(min(rem, max_val), 0, -1):
        gen_partitions_8(rem - d, d, current + [d])
gen_partitions_8(8, 8, [])

print("Checking 7...")
def check_partition_7(p):
    s7 = sum(S(7 * d) for d in p)
    if s7 != 7: return False
    for k in range(8, 3000):
        if k == 9: continue
        sk = sum(S(k * d) for d in p)
        if sk == k: return False
    return True

def gen_partitions_7(rem, max_val, current):
    if rem == 0:
        if check_partition_7(current):
            print(f"FOUND COUNTEREXAMPLE PARTITION FOR 7: {current}")
        return
    for d in range(min(rem, max_val), 0, -1):
        gen_partitions_7(rem - d, d, current + [d])
gen_partitions_7(7, 7, [])

print("Done")
