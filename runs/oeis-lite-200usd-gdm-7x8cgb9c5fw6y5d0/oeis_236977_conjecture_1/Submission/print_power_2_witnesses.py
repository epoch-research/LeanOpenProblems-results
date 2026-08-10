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

for a in range(4, 21):
    n = 2**a
    found = []
    for k in range(1, (n - 1) // 2 + 1):
        if is_square(totient(k) * totient(n - k)):
            found.append(k)
    print(f"n = 2^{a:2d} = {n:7d} : witnesses = {found[:10]}")
