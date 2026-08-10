def choose(n, k):
    import math
    return math.comb(n, k)

def a(n):
    S1 = sum(choose(n + k - 1, k) for k in range(2 * n + 1))
    S2 = sum(choose(n + k - 1, k)**2 for k in range(2 * n + 1))
    return S1**4 * S2**3

for n in range(1, 6):
    print(f"a({n}) = {a(n)}")
