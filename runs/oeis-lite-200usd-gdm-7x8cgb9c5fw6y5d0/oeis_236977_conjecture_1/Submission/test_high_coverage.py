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

good_c = []
for c in range(2, 10000):
    if is_square(totient(c)):
        good_c.append(c)

print(f"Total good c up to 10000: {len(good_c)}")

# Let's see the coverage of the first K good c values on [9, 2000000]
# We can use a bitset or boolean array for coverage
limit = 2000000
covered = [False] * (limit + 1)

# Cover by base rules
for n in range(9, limit + 1):
    if n % 6 == 3 or n % 10 == 0 or n % 6 == 0:
        covered[n] = True

initial_uncovered = sum(1 for n in range(9, limit + 1) if not covered[n])
print(f"Initial uncovered: {initial_uncovered}")

# We will apply c values one by one and see how coverage grows
count = 0
for c in good_c:
    c_plus_1 = c + 1
    # We only need to check multiples of c+1
    for n in range(c_plus_1 * ((9 + c_plus_1 - 1) // c_plus_1), limit + 1, c_plus_1):
        if not covered[n]:
            if math.gcd(c, n // c_plus_1) == 1:
                covered[n] = True
                count += 1
    # print coverage every 50 c's
    if c in good_c[:10] or good_c.index(c) % 50 == 0:
        uncovered = sum(1 for n in range(9, limit + 1) if not covered[n])
        print(f"After c={c} (index {good_c.index(c)}): uncovered = {uncovered}")

uncovered = sum(1 for n in range(9, limit + 1) if not covered[n])
print(f"Final uncovered: {uncovered}")
