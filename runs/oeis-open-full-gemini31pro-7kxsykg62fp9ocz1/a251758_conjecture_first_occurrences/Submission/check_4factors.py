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

c4 = []
c5 = []
for n in range(17, 6678672, 2):
    if n % 3 == 0 or n % 5 == 0 or n % 7 == 0 or n % 11 == 0 or n % 13 == 0: continue
    c = count_prime_factors(n)
    if c >= 4:
        c4.append(n)
    if c >= 5:
        c5.append(n)

print(">= 4 prime factors:", len(c4))
print(">= 5 prime factors:", len(c5))
