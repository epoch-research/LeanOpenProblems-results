def S(m):
    return sum(int(c) for c in str(m))

for a in range(20):
    for b in range(20):
        val = 6 * 10**a + 10**b
        if val % 7 == 0:
            print(f"6 and 1: a={a}, b={b}, val={val}, n={val//7}")
