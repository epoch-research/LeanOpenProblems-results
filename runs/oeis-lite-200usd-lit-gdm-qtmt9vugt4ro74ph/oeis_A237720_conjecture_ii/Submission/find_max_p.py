import math

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.isqrt(n)) + 1):
        if n % i == 0: return False
    return True

primes = [p for p in range(2, 200000) if is_prime(p)]
prime_set = set(primes)

max_p = 0
for n in range(3, 100000):
    found = False
    for p in primes:
        if p >= n:
            break
        if math.isqrt(n + p) in prime_set:
            max_p = max(max_p, p)
            found = True
            break
    if not found:
        print(f"No p found for n = {n}")

print(f"Max p needed: {max_p}")
