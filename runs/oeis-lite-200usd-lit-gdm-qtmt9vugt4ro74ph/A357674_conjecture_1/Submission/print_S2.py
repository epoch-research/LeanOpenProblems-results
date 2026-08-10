def choose(n, k):
    import math
    return math.comb(n, k)

def S2(n):
    return sum(choose(n + k - 1, k)**2 for k in range(2 * n + 1))

for n in range(1, 6):
    print(f"S2({n}) = {S2(n)}")
