import math

# Sieve to find primes and totients
limit = 2000005
phi = list(range(limit))
is_prime = [True] * limit
is_prime[0] = is_prime[1] = False
for i in range(2, limit):
    if phi[i] == i:
        for j in range(i, limit, i):
            phi[j] -= phi[j] // i
            if j > i:
                is_prime[j] = False

def is_square(x):
    r = int(math.isqrt(x))
    return r * r == x

# Find additive partitions for primes up to 100
prime_partitions = {}
for p in range(2, 100):
    if is_prime[p]:
        # find first partition (a, b) such that phi(a)*phi(b) is square
        for a in range(1, (p - 1) // 2 + 1):
            b = p - a
            if is_square(phi[a] * phi[b]):
                prime_partitions[p] = (a, b)
                break

print(f"Primes with partition: {list(prime_partitions.keys())}")

# Let's count coverage on [9, 2000000]
uncovered_composites = 0
uncovered_primes = 0

# Base coverage by mod 6 and mod 10 rules
covered = [False] * (limit + 1)
for n in range(9, limit + 1):
    if n % 6 == 3 or n % 10 == 0 or n % 6 == 0:
        covered[n] = True

# Apply the additive partitions
for p, (a, b) in prime_partitions.items():
    # n must be a multiple of p
    for n in range(p * ((9 + p - 1) // p), limit + 1, p):
        if not covered[n]:
            m = n // p
            # check Coprime (a*b) m
            if math.gcd(a * b, m) == 1:
                covered[n] = True

for n in range(9, limit):
    if not covered[n]:
        if is_prime[n]:
            uncovered_primes += 1
        else:
            uncovered_composites += 1

print(f"Remaining uncovered composites: {uncovered_composites}")
print(f"Remaining uncovered primes: {uncovered_primes}")
print(f"Total uncovered: {uncovered_composites + uncovered_primes}")
