import math

def is_prime(n):
    if n < 2: return False
    for i in range(2, int(math.sqrt(n))+1):
        if n % i == 0: return False
    return True

# We want to find any q^f - p^e = 2 where p, q are prime and e, f > 1.
# This is equivalent to q^f = p^e + 2.
# Let's search over all p^e up to 10^14.
# We can iterate over all prime powers p^e.
# For each p, we can iterate over e >= 2.
max_val = 10**14
found = []

primes = []
for p in range(2, 10000000):
    if is_prime(p):
        primes.append(p)

print(f"Generated {len(primes)} primes.")

# To search efficiently, we can store all q^f in a set, or just check if p^e + 2 is a prime power.
# Let's do: for each prime p, and e >= 2:
# check if val = p^e + 2 is a prime power q^f with f >= 2.

def is_prime_power(n):
    if n < 2: return None
    # check for each f >= 2
    # n = q^f => q = n^(1/f)
    for f in range(2, int(math.log2(n))+2):
        # find closest integer root
        q_cand = int(round(n**(1/f)))
        if q_cand**f == n:
            if is_prime(q_cand):
                return q_cand, f
    return None

for p in primes:
    e = 2
    while True:
        val = p**e
        if val > max_val:
            break
        target = val + 2
        res = is_prime_power(target)
        if res is not None:
            q, f = res
            print(f"FOUND: {q}^{f} - {p}^{e} = 2")
            found.append((p, e, q, f))
        e += 1

print("Search complete. Found:", found)
