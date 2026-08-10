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

# Find partitions for all primes up to limit
# To make it super fast, we only search a up to min(50, (p-1)//2) first
# if not found, we search further.
print("Finding prime partitions...", flush=True)
prime_partitions = {}
uncovered_primes = []
for p in range(2, limit):
    if is_prime[p]:
        if p in [2, 5]:
            continue
        found = False
        # Phase 1: search a up to 100
        for a in range(1, min(100, (p - 1) // 2 + 1)):
            b = p - a
            if is_square(phi[a] * phi[b]):
                prime_partitions[p] = (a, b)
                found = True
                break
        if not found:
            # Phase 2: search a up to (p-1)//2
            for a in range(100, (p - 1) // 2 + 1):
                b = p - a
                if is_square(phi[a] * phi[b]):
                    prime_partitions[p] = (a, b)
                    found = True
                    break
        if not found:
            uncovered_primes.append(p)

print(f"Partitions found for {len(prime_partitions)} primes.")
print(f"Primes without partitions: {len(uncovered_primes)}")
if len(uncovered_primes) > 0:
    print(f"Primes without partitions: {uncovered_primes[:50]}")

uncovered = []
for n in range(9, 2000000 + 1):
    if n % 3 == 0 or n % 10 == 0:
        continue
        
    # Check if n has a partition itself (if prime)
    if is_prime[n]:
        if n in prime_partitions:
            continue
        else:
            uncovered.append(n)
            continue
            
    # If composite: find a prime factor p of n that is in prime_partitions
    # and satisfies the gcd conditions
    temp = n
    found = False
    # Check prime factors of n
    # We can just factorize n
    temp = n
    d = 2
    factors = []
    while d * d <= temp:
        if temp % d == 0:
            factors.append(d)
            while temp % d == 0:
                temp //= d
        d += 1
    if temp > 1:
        factors.append(temp)
        
    for p in factors:
        if p in prime_partitions:
            a, b = prime_partitions[p]
            if math.gcd(a, n // p) == 1 and math.gcd(b, n // p) == 1:
                found = True
                break
                
    if not found:
        uncovered.append(n)

print(f"Total uncovered after partition rule: {len(uncovered)}")
if len(uncovered) > 0:
    print(f"First 100 uncovered: {uncovered[:100]}")
