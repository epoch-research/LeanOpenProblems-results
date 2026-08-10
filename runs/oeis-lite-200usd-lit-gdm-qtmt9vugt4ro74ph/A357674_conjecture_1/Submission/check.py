def choose(n, k):
    if k < 0 or k > n:
        return 0
    import math
    return math.comb(n, k)

def test(p):
    S1 = sum(choose(p + k - 1, k) for k in range(2 * p + 1))
    S2 = sum(choose(p + k - 1, k)**2 for k in range(2 * p + 1))
    val = (3 * S2 + 4 * S1) % (p**5)
    print(f"p = {p}:")
    print(f"  S1 = {S1}")
    print(f"  S2 = {S2}")
    print(f"  S1 mod p^5 = {S1 % (p**5)}")
    print(f"  S2 mod p^5 = {S2 % (p**5)}")
    print(f"  3*S2 + 4*S1 = {3*S2 + 4*S1}")
    print(f"  3*S2 + 4*S1 mod p^5 = {val}")

for p in [3, 5, 7, 11]:
    test(p)
