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

# Precompute which primes p have phi(p-1) as a perfect square
good_primes = []
for p in range(2, limit):
    if is_prime[p]:
        if is_square(phi[p - 1]):
            good_primes.append(p)

print(f"Total good primes up to {limit}: {len(good_primes)}")
print(f"First few good primes: {good_primes[:20]}")

# Let's check how many numbers up to 2,000,000 are:
# 1. Prime
# 2. Composite, and have at least one prime factor p in good_primes
# 3. Composite, and have NO prime factor in good_primes

count_primes = 0
count_composite_good_factor = 0
count_composite_no_good_factor = 0

# To make it fast, we can factor or check
# For each n, we can check if any prime factor is in good_primes
# Actually, we can just mark multiples of good_primes!
has_good_prime_factor = [False] * (limit + 1)
for p in good_primes:
    for j in range(p, limit + 1, p):
        has_good_prime_factor[j] = True

for n in range(9, limit):
    if is_prime[n]:
        count_primes += 1
    else:
        if has_good_prime_factor[n]:
            count_composite_good_factor += 1
        else:
            count_composite_no_good_factor += 1

print(f"Total primes: {count_primes}")
print(f"Composite with good prime factor: {count_composite_good_factor}")
print(f"Composite with NO good prime factor: {count_composite_no_good_factor}")
