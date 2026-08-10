import math

# Fast totient
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

# Find first prime partition for all primes up to 1414 (excluding 2 and 5)
prime_partitions = {}
for p in range(2, 1415):
    if is_prime[p] and p not in [2, 5]:
        for a in range(1, (p - 1) // 2 + 1):
            b = p - a
            if is_square(phi[a] * phi[b]):
                prime_partitions[p] = (a, b)
                break

print(f"Found prime partitions for {len(prime_partitions)} primes.")

covered = [False] * limit
for n in range(9, limit):
    if n % 3 == 0 or n % 10 == 0:
        covered[n] = True

# We sort primes descending to apply largest prime factors first or vice versa.
# Actually we can just apply them
for p, (a, b) in prime_partitions.items():
    ab = a * b
    for n in range(p * ((9 + p - 1) // p), limit, p):
        if not covered[n]:
            m = n // p
            if math.gcd(ab, m) == 1:
                covered[n] = True

uncovered = [n for n in range(9, 2000000 + 1) if not covered[n]]
print(f"Total uncovered after applying all rules: {len(uncovered)}")
print(f"First 50 uncovered: {uncovered[:50]}")
