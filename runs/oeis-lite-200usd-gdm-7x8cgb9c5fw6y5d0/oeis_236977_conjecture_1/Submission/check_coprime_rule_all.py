import math

def totient(n):
    t = n
    p = 2
    temp = n
    while p * p <= temp:
        if temp % p == 0:
            while temp % p == 0:
                temp //= p
            t -= t // p
        if p == 2:
            p = 3
        else:
            p += 2
    if temp > 1:
        t -= t // temp
    return t

def is_square(x):
    r = int(math.isqrt(x))
    return r * r == x

# Find all c up to 10000 such that totient(c) is a perfect square
good_c = []
for c in range(1, 10000):
    if is_square(totient(c)):
        good_c.append(c)

print(f"Found {len(good_c)} values of c with square totients.")

# Sieve to find primes
limit = 2000005
is_prime = [True] * limit
is_prime[0] = is_prime[1] = False
for i in range(2, int(math.isqrt(limit)) + 1):
    if is_prime[i]:
        for j in range(i*i, limit, i):
            is_prime[j] = False

# We check how many composite numbers we can cover
uncovered_composites = 0
total_composites = 0

for n in range(9, 2000000 + 1):
    if is_prime[n]:
        continue
    
    total_composites += 1
    
    # Check if n % 6 == 3 or n % 10 == 0 or n % 6 == 0
    if n % 6 == 3 or n % 10 == 0 or n % 6 == 0:
        continue
        
    # Check if n is covered by the coprime rule
    covered = False
    for c in good_c:
        if n % (c + 1) == 0:
            m = n // (c + 1)
            if math.gcd(c, m) == 1:
                covered = True
                break
    if not covered:
        uncovered_composites += 1

print(f"Total composites: {total_composites}")
print(f"Uncovered composites: {uncovered_composites}")
print(f"Fraction covered: {1 - uncovered_composites / total_composites:.4f}")
