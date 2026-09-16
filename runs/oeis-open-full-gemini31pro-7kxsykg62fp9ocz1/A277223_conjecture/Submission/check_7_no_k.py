def S(m):
    return sum(int(c) for c in str(m))

def find_counterexample():
    import itertools
    # generate x with S(x)=7, x % 7 == 0
    # represent x by the positions of its digits.
    # sum of digits is 7, so up to 7 non-zero digits.
    count = 0
    for p in itertools.combinations_with_replacement(range(35), 7):
        val = sum(10**pos for pos in p)
        if val % 7 == 0:
            n = val // 7
            count += 1
            max_k = 0
            for k in range(8, 200):
                if S(k * n) == k:
                    max_k = k
                    break
            if max_k == 0:
                # check up to 1000
                for k in range(200, 1000):
                    if S(k * n) == k:
                        max_k = k
                        break
                if max_k == 0:
                    print(f"FOUND! n={n}, x={val}")
                    return
    print(f"Checked {count} numbers, no counterexample.")

find_counterexample()
