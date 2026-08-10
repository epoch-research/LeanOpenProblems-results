import math

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

# We find partitions for primes in [7, 11, 13, 17, 19, 23, 29, 31]
good_primes = [7, 11, 13, 17, 19, 23, 29, 31]
prime_partitions = {}
for p in good_primes:
    for a in range(1, (p - 1) // 2 + 1):
        b = p - a
        if is_square(phi[a] * phi[b]):
            prime_partitions[p] = (a, b)
            break

print("Partitions found:", prime_partitions)

covered = [False] * limit
for n in range(9, limit):
    if n % 3 == 0 or n % 10 == 0:
        covered[n] = True

# Apply prime partition rules for good_primes
for p, (a, b) in prime_partitions.items():
    ab = a * b
    for n in range(p * ((9 + p - 1) // p), limit, p):
        if not covered[n]:
            m = n // p
            if math.gcd(ab, m) == 1:
                covered[n] = True

# Count uncovered composites and primes separately
uncovered_composites = []
uncovered_primes = []

for n in range(9, 2000000 + 1):
    if not covered[n]:
        if is_prime[n]:
            uncovered_primes.append(n)
        else:
            uncovered_composites.append(n)

print(f"Remaining uncovered primes: {len(uncovered_primes)}")
print(f"Remaining uncovered composites: {len(uncovered_composites)}")
print(f"Total uncovered: {len(uncovered_primes) + len(uncovered_composites)}")
print(f"First 50 uncovered composites: {uncovered_composites[:50]}")
