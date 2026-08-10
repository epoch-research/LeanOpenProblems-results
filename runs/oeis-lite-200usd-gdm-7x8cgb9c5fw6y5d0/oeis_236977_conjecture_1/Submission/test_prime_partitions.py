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

# Find primes up to 200
primes = []
for p in range(2, 200):
    is_p = True
    for d in range(2, int(math.isqrt(p)) + 1):
        if p % d == 0:
            is_p = False
            break
    if is_p:
        primes.append(p)

print("Prime p : (a, b) such that phi(a)*phi(b) is square")
found_count = 0
for p in primes:
    partitions = []
    for a in range(1, (p - 1) // 2 + 1):
        b = p - a
        if is_square(totient(a) * totient(b)):
            partitions.append((a, b))
    if partitions:
        print(f"p = {p:3d} : {partitions}")
        found_count += 1
    else:
        print(f"p = {p:3d} : NONE")

print(f"Found partitions for {found_count} out of {len(primes)} primes.")
