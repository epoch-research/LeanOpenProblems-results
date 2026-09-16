def S(m):
    return sum(int(c) for c in str(m))

for n in range(1, 10000):
    if S(6*n) == 6:
        x = 6*n
        valid = [k for k in range(7, 200) if S(k*n) == k]
        print(f"x={x}, n={n}, max_digit_x={max(int(d) for d in str(x))}, valid={valid[:3]}")
