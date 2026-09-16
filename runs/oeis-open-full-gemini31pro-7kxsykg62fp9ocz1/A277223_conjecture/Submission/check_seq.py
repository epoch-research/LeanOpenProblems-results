def S(m):
    return sum(int(c) for c in str(m))

def seq(n, start):
    k = start
    seen = set()
    while k not in seen:
        seen.add(k)
        k = S(k * n)
    return k # this is a cycle. Is it a fixed point?

for n in range(1, 1000, 9):
    k = seq(n, 9)
    if S(k * n) != k:
        print(f"n={n} has a cycle of length > 1! {k}")
    if k < 9:
        print(f"n={n}, fixed point {k} < 9")
