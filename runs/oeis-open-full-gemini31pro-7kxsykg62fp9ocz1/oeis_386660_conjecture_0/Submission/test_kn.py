import math

def get_kn(n):
    for k in range(n, -1, -1):
        if math.comb(n, k) >= 2**k:
            return k
    return 0

for n in [10, 100, 1000, 10000, 100000]:
    kn = get_kn(n)
    print(f"n={n}, kn={kn}, kn/n={kn/n:.5f}")
