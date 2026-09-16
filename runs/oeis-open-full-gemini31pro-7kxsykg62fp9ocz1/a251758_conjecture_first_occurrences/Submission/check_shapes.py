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

def get_a(n):
    divs = []
    for i in range(1, int(math.isqrt(n)) + 1):
        if n % i == 0:
            divs.append(i)
            if i * i != n:
                divs.append(n // i)
    divs.sort()
    s = 0
    for i in range(len(divs) - 1):
        s += divs[i] * divs[i+1]
    if s == 0: return 0
    return (n * n) // s

for n in range(17, 6678672, 2):
    if n % 3 == 0 or n % 5 == 0 or n % 7 == 0 or n % 11 == 0 or n % 13 == 0: continue
    if count_prime_factors(n) >= 4:
        a = get_a(n)
        if a <= 14:
            print(f"n={n}, a={a}")
