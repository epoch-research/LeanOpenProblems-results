import math

def choose(n, k):
    return math.comb(n, k)

def b(n, k):
    val = n + k - 1
    if val < 0:
        val = 0
    return choose(val, k)

def u(n, m):
    total = 0
    for k in range(m * n + 1):
        bk = b(n, k)
        term = (m + 2) * bk**2 + (2 * m) * bk**3
        total += term
    return total

p = 3
r = 2
modulus = p**(3*r + 3) # 19683

for m in range(1, 6):
    val1 = u(p**r, m)
    val2 = u(p**(r-1), m)
    print(f"m = {m}:")
    print(f"  u({p**r}, {m}) = {val1}")
    print(f"  u({p**(r-1)}, {m}) = {val2}")
    print(f"  Is congruent? {(val1 - val2) % modulus == 0}")
