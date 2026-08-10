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

# The 18 uncovered classes modulo 30
uncovered = [1, 2, 4, 5, 7, 8, 11, 13, 14, 16, 17, 19, 22, 23, 25, 26, 28, 29]

# We will search for d up to 1000, and find if we can cover every number.
# Actually, let's keep track of which specific integers in [9, 200000] are NOT covered by our rules.
# Initially, the uncovered integers are those in the 18 classes.
uncovered_set = set()
for n in range(9, 200001):
    if n % 6 == 3 or n % 10 == 0 or n % 6 == 0:
        continue
    uncovered_set.add(n)

print(f"Initially uncovered in [9, 200000]: {len(uncovered_set)}")

# Let's search for rules of the form n % d == r, k = c*m + e, where n = d*m + r.
# To make it easy to verify, we'll check if it works for all m up to 200.
# We will iterate over d and r.
# To be efficient, we only consider d that can cover some elements of uncovered_set.
discovered_rules = []

# Let's check d up to 150
for d in range(12, 151):
    # Only consider d with some small factors
    if math.gcd(d, 30) == 1:
        continue
    for r in range(d):
        # Check if this class contains any uncovered elements
        elements = [n for n in range(r, 200001, d) if n in uncovered_set]
        if not elements:
            continue
        # Search for c, e
        for c in range(1, d // 2 + 1):
            # We can search e in a range
            for e in range(-30, 31):
                works = True
                # test for a range of m
                for m in range(1, 200):
                    n = d * m + r
                    if n < 9:
                        continue
                    k = c * m + e
                    if not (1 <= k < (n - 1) // 2 + 1):
                        works = False
                        break
                    prod = totient(k) * totient(n - k)
                    if not is_square(prod):
                        works = False
                        break
                if works:
                    print(f"FOUND RULE: n % {d} == {r}, k = {c}*m + ({e}) covers {len(elements)} elements")
                    discovered_rules.append((d, r, c, e))
                    # Remove covered elements
                    for el in elements:
                        uncovered_set.discard(el)
                    break
            if works:
                break

print(f"Remaining uncovered in [9, 200000]: {len(uncovered_set)}")
if len(uncovered_set) > 0:
    print(f"First 100 remaining: {sorted(list(uncovered_set))[:100]}")
