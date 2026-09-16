import math

def count_prime_factors(n):
    c = 0
    d = 17
    while d * d <= n:
        while (n % d) == 0:
            c += 1
            n //= d
        d += 2
    if n > 1:
        c += 1
    return c

c3 = []
for n in range(17, 6678672, 2):
    if n % 3 == 0 or n % 5 == 0 or n % 7 == 0 or n % 11 == 0 or n % 13 == 0: continue
    if count_prime_factors(n) >= 3:
        c3.append(n)

print("Numbers with >= 3 prime factors:", len(c3))
