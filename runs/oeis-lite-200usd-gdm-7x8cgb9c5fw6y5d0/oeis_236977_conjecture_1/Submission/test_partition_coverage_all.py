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

# We find partitions for all primes up to 2000
primes_2000 = [p for p in range(2, 2000) if is_prime[p] and p not in [2, 5]]
prime_partitions = {}
for p in primes_2000:
    for a in range(1, (p - 1) // 2 + 1):
        b = p - a
        if is_square(phi[a] * phi[b]):
            prime_partitions[p] = (a, b)
            break

print(f"Partitions found for {len(prime_partitions)} primes.")

uncovered = []
for n in range(9, 2000000 + 1):
    if n % 3 == 0 or n % 10 == 0:
        continue
    
    # Try to find a prime factor p of n that is in prime_partitions
    # and satisfies the gcd conditions
    temp = n
    found = False
    for p in primes_2000:
        if p * p > temp:
            if temp > 1 and temp in prime_partitions:
                a, b = prime_partitions[temp]
                if math.gcd(a, n // temp) == 1 and math.gcd(b, n // temp) == 1:
                    found = True
                    break
            break
        if temp % p == 0:
            while temp % p == 0:
                temp //= p
            if p in prime_partitions:
                a, b = prime_partitions[p]
                if math.gcd(a, n // p) == 1 and math.gcd(b, n // p) == 1:
                    found = True
                    break
                    
    if not found:
        uncovered.append(n)

print(f"Total uncovered after partition rule: {len(uncovered)}")
print(f"First 100 uncovered: {uncovered[:100]}")
