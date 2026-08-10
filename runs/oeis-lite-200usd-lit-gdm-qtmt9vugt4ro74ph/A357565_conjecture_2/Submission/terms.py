import math

def choose(n, k):
    if k < 0 or k > n:
        return 0
    return math.comb(n, k)

def A357565(n):
    total = 0
    for k in range(n + 1):
        val = n + k - 1
        if val < 0:
            val = 0
        b = choose(val, k)
        term = 3 * b**2 + 2 * b**3
        total += term
    return total

for p in [3, 5, 7]:
    for r in [2, 3]:
        val1 = A357565(p**r)
        val2 = A357565(p**(r-1))
        modulus = p**(3*r + 3)
        diff = val1 - val2
        rem = diff % modulus
        print(f"p={p}, r={r}, modulus={modulus}:")
        print(f"  A(p^r) = {val1}")
        print(f"  A(p^(r-1)) = {val2}")
        print(f"  Rem = {rem}")
        print(f"  Divisible? {rem == 0}")

