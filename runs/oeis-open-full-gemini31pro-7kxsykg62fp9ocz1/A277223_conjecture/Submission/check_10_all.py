def S(m):
    return sum(int(c) for c in str(m))

def get_n(rem, current_val, p10):
    if rem == 0:
        yield current_val
        return
    # to avoid 0s and 1s only, we can just enumerate all
    for d in range(0, rem + 1):
        if d == 0 and current_val == 0:
            continue # no trailing zeros? Actually zeros don't change S(n)
        yield from get_n(rem - d, current_val + d * p10, p10 * 10)

def search():
    for length in range(1, 12):
        print(f"Length {length}")
        def gen(rem, l, acc):
            if l == 0:
                if rem == 0:
                    yield int("".join(map(str, acc)))
                return
            for d in range(10):
                if d <= rem:
                    if d == 0 and acc == []:
                        continue
                    yield from gen(rem - d, l - 1, acc + [d])
        
        for n in gen(10, length, []):
            max_k = 0
            for k in range(11, 200):
                if S(k * n) == k:
                    max_k = k
                    break
            if max_k == 0: # means no k in 11..199
                # let's check up to 1000 just in case
                for k in range(200, 1000):
                    if S(k * n) == k:
                        max_k = k
                        break
                if max_k == 0:
                    print(f"COUNTEREXAMPLE: n={n}")
                    return

search()
print("Done")
