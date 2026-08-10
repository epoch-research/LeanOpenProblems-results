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

# Find all c < 5000 with totient c being a perfect square
good_c = []
for c in range(2, 5000):
    if is_square(totient(c)):
        good_c.append(c)

print(f"Total good c: {len(good_c)}")

# Let's see which c are most useful on the range [9, 200000]
# We'll do a greedy selection of c to see how many we need to get very high coverage.
limit = 200000
uncovered = set()
for n in range(9, limit + 1):
    if n % 6 == 3 or n % 10 == 0 or n % 6 == 0:
        continue
    uncovered.add(n)

print(f"Initial uncovered in [9, {limit}]: {len(uncovered)}")

# Greedy selection
selected_c = []
while len(uncovered) > 0 and len(selected_c) < 30:
    best_c = None
    best_cover = set()
    for c in good_c:
        if c in selected_c:
            continue
        cover = set()
        c_plus_1 = c + 1
        for n in uncovered:
            if n % c_plus_1 == 0:
                if math.gcd(c, n // c_plus_1) == 1:
                    cover.add(n)
        if len(cover) > len(best_cover):
            best_cover = cover
            best_c = c
    if not best_c or len(best_cover) == 0:
        break
    selected_c.append(best_c)
    uncovered -= best_cover
    print(f"Selected c={best_c} (covers {len(best_cover)} more, remaining: {len(uncovered)})")

print(f"Final selected c: {selected_c}")
