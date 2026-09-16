def S(m):
    return sum(int(c) for c in str(m))

for n in range(1, 1000000):
    if n % 9 == 1:
        # check max valid multiplier
        max_k = 0
        for k in range(1, 120):
            if S(k * n) == k:
                max_k = k
        if max_k > 0 and max_k < 12 and max_k != 9:
            # wait, we must make sure NO k > 120 is valid
            valid_larger = False
            for k in range(120, 500):
                if S(k * n) == k:
                    valid_larger = True
                    break
            if not valid_larger:
                print(f"COUNTEREXAMPLE FOUND: n={n}, max_k={max_k}")
                exit(0)
print("Not found up to 1000000")
