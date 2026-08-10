import math

limit = 2000005
is_prime = [True] * limit
is_prime[0] = is_prime[1] = False
for i in range(2, int(math.isqrt(limit)) + 1):
    if is_prime[i]:
        for j in range(i*i, limit, i):
            is_prime[j] = False

# We'll find the smallest prime factor of each number
# To make it fast, we can use a sieve for spf (smallest prime factor)
spf = list(range(limit))
for i in range(2, int(math.isqrt(limit)) + 1):
    if spf[i] == i:
        for j in range(i*i, limit, i):
            if spf[j] == j:
                spf[j] = i

# Let's count how many n in [9, 2,000,000] are:
# - Coprime to 6, and coprime to 10
# - And have spf(n) >= 211
uncovered = []
for n in range(9, 2000000 + 1):
    # Rule 1, 2, 3 cover:
    if n % 6 == 3 or n % 10 == 0 or n % 6 == 0:
        continue
    
    # Otherwise, what is the smallest prime factor?
    q = spf[n]
    if q >= 211:
        uncovered.append(n)

print(f"Total uncovered numbers: {len(uncovered)}")
print(f"First 50 uncovered: {uncovered[:50]}")
