import math

def totient(n):
    t = n
    p = 2
    temp = n
    while p * p <= temp:
        if temp % p == 0:
            while temp % p == 0:
                temp //= p
            t -= t // p
        if p == 2:
            p = 3
        else:
            p += 2
    if temp > 1:
        t -= t // temp
    return t

def is_square(x):
    r = int(math.isqrt(x))
    return r * r == x

# Find primes up to 1414
limit = 1414
phi = [totient(i) for i in range(limit + 1)]
is_prime = [True] * (limit + 1)
is_prime[0] = is_prime[1] = False
for i in range(2, limit + 1):
    if is_prime[i]:
        for j in range(i*i, limit + 1, i):
            is_prime[j] = False

primes = [p for p in range(limit + 1) if is_prime[p]]

unpartitionable = []
for p in primes:
    if p in [2, 5]:
        continue
    found = False
    for a in range(1, (p - 1) // 2 + 1):
        b = p - a
        if is_square(phi[a] * phi[b]):
            found = True
            break
    if not found:
        unpartitionable.append(p)

print(f"Unpartitionable primes up to 1414 (excluding 2 and 5): {unpartitionable}")
