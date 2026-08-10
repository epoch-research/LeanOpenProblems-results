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

# Find primes
limit = 2000
phi = [totient(i) for i in range(limit)]
is_prime = [True] * limit
is_prime[0] = is_prime[1] = False
for i in range(2, limit):
    if is_prime[i]:
        for j in range(i*i, limit, i):
            is_prime[j] = False

primes = [n for n in range(9, limit) if is_prime[n]]

print("Prime n : smallest witness k")
for n in primes[:50]:
    for k in range(1, (n - 1) // 2 + 1):
        if is_square(phi[k] * phi[n - k]):
            print(f"n = {n:4d} (phi={phi[n-1]:4d}) : k = {k:2d} (phi(k)={phi[k]:2d}, phi(n-k)={phi[n-k]:2d}, prod={phi[k]*phi[n-k]:4d})")
            break
