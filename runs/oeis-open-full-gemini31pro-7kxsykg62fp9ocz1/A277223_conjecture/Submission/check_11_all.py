def S(m):
    return sum(int(c) for c in str(m))

def search():
    for length in range(1, 10):
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
        
        for p in gen(11, length, []):
            if p % 11 != 0: continue
            n = p // 11
            max_k = 0
            for k in range(12, 100):
                if S(k * n) == k:
                    max_k = k
                    break
            if max_k == 0:
                # check further
                for k in range(100, 1000):
                    if S(k * n) == k:
                        max_k = k
                        break
                if max_k == 0:
                    print(f"COUNTEREXAMPLE: n={n}")
                    return

search()
print("Done")
