def S(m):
    return sum(int(c) for c in str(m))
for m in range(1, 50):
    n = (10**m - 1) // 9
    valid = [k for k in range(1, 200) if S(k*n) == k]
    print(f"n=1..1 (len {m}), valid={valid}")
