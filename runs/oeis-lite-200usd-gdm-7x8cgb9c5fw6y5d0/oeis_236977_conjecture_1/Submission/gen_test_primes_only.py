import math

limit = 100005
phi = list(range(limit))
is_prime = [True] * limit
is_prime[0] = is_prime[1] = False
for i in range(2, limit):
    if phi[i] == i:
        for j in range(i, limit, i):
            phi[j] -= phi[j] // i
            if j > i:
                is_prime[j] = False

spf = list(range(limit))
for i in range(2, int(math.isqrt(limit)) + 1):
    if spf[i] == i:
        for j in range(i*i, limit, i):
            if spf[j] == j:
                spf[j] = i

def is_square(x):
    r = int(math.isqrt(x))
    return r * r == x

def find_partition(p):
    for a in range(1, (p - 1) // 2 + 1):
        b = p - a
        if is_square(phi[a] * phi[b]):
            return a, b
    return None

uncovered_composites = []
for n in range(9, 1000 + 1):
    if n % 6 == 3 or n % 10 == 0 or n % 6 == 0:
        continue
    if is_prime[n]:
        continue
    
    p = spf[n]
    part = find_partition(p)
    if part is None:
        uncovered_composites.append((n, p, "no partition"))
        continue
    a, b = part
    m = n // p
    if math.gcd(a * b, m) != 1:
        uncovered_composites.append((n, p, f"gcd({a}*{b}, {m}) != 1"))

print(f"Sample of uncovered composites up to 1000: {uncovered_composites[:20]}")
