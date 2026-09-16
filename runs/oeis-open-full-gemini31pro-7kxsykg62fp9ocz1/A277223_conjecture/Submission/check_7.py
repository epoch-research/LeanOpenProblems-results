def S(m):
    return sum(int(c) for c in str(m))

def check():
    import itertools
    for p in itertools.combinations_with_replacement(range(18), 7):
        val = sum(10**x for x in p)
        if val % 7 == 0:
            n = val // 7
            max_k = 0
            for k in range(1, 100):
                if S(k * n) == k:
                    max_k = k
            if max_k == 7:
                print(f"Counterexample! n={n}, max_k=7")
                return
    print("No counterexample up to 18.")

check()
