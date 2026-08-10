import math

def choose(n, k):
    return math.comb(n, k)

def u(n, m):
    total = 0
    for k in range(m * n + 1):
        b = choose(n + k - 1, k)
        term = (m + 2) * b**2 + (2 * m) * b**3
        total += term
    return total

p = 3
for r in [2, 3]:
    mod1 = p**(3*r + 3)
    mod2 = p**(2*r + 2)
    val1 = u(p**r, 1)
    val2 = u(p**(r-1), 1)
    print(f"r={r}:")
    print(f"  u(p^r, 1) - u(p^(r-1), 1) % p^(3r+3): {(val1 - val2) % mod1}")
    print(f"  u(p^r, 1) - u(p^(r-1), 1) % p^(2r+2): {(val1 - val2) % mod2}")
