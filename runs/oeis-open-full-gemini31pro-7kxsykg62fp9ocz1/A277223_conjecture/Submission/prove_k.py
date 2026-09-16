def S(m):
    return sum(int(c) for c in str(m))

for n in range(1, 1000):
    if n % 9 == 1:
        valid = [k for k in range(1, 200) if S(k * n) == k]
        if valid and max(valid) < 9:
            print(f"Counterexample! n={n}, max={max(valid)}")
