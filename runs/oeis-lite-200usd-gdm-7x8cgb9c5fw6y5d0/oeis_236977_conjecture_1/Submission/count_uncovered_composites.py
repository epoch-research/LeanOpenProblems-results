import math

# Sieve to find primes
limit = 2000005
is_prime = [True] * limit
is_prime[0] = is_prime[1] = False
for i in range(2, int(math.isqrt(limit)) + 1):
    if is_prime[i]:
        for j in range(i*i, limit, i):
            is_prime[j] = False

# List of c values
good_c = [10, 12, 34, 40, 48, 60, 85, 108, 114, 126, 136, 160, 170, 185, 192, 202, 204, 240, 250, 273, 285, 292, 304, 315, 364, 451, 505, 513, 577]

def is_uncovered(n):
    if n % 6 == 3:
        return False
    if n % 10 == 0:
        return False
    if n % 6 == 0:
        return False
    
    # rule_coprime c
    for c in good_c:
        if n % (c + 1) == 0:
            if math.gcd(c, n // (c + 1)) == 1:
                return False
    return True

total_composite = 0
uncovered_composite = 0
uncovered_primes = 0

for n in range(9, 2000000 + 1):
    if is_prime[n]:
        if is_uncovered(n):
            uncovered_primes += 1
    else:
        total_composite += 1
        if is_uncovered(n):
            uncovered_composite += 1

print(f"Total composites: {total_composite}")
print(f"Uncovered composites: {uncovered_composite}")
print(f"Uncovered primes: {uncovered_primes}")
print(f"Total uncovered: {uncovered_composite + uncovered_primes}")
