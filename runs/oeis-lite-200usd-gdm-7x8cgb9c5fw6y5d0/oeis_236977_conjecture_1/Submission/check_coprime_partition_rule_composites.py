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

# Find first prime partition for all primes up to 1414
prime_partitions = {}
for p in range(2, 1415):
    if is_prime[p] and p not in [2, 5]:
        for a in range(1, (p - 1) // 2 + 1):
            b = p - a
            if is_square(phi[a] * phi[b]):
                prime_partitions[p] = (a, b)
                break

# List of primes up to 2000
primes_list = [p for p in range(2, limit) if is_prime[p]]

uncovered_composites = []

# Check all composite n up to 2,000,000
# not divisible by 3 or 10
print("Sieve done. Checking composites...", flush=True)
count = 0
for n in range(9, 2000001):
    if n % 3 == 0 or n % 10 == 0:
        continue
    if is_prime[n]:
        continue
        
    count += 1
    # Find a prime factor p of n that has a partition (a, b)
    # such that gcd(a * b, n / p) == 1
    # We only check prime factors p of n
    temp = n
    found = False
    for p in primes_list:
        if p * p > temp and temp > 1:
            # temp is prime
            p_factor = temp
            if p_factor in prime_partitions:
                a, b = prime_partitions[p_factor]
                if math.gcd(a * b, n // p_factor) == 1:
                    found = True
                    break
            break
        if temp % p == 0:
            while temp % p == 0:
                temp //= p
            if p in prime_partitions:
                a, b = prime_partitions[p]
                if math.gcd(a * b, n // p) == 1:
                    found = True
                    break
    if not found:
        uncovered_composites.append(n)
        if len(uncovered_composites) < 50:
            print(f"Uncovered composite: {n}")
            
print(f"Total composites checked: {count}")
print(f"Uncovered composites: {len(uncovered_composites)}")
