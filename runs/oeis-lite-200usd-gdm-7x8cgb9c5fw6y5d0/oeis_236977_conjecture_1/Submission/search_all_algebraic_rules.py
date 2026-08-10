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

print("Searching for algebraic rules for uncovered classes...")

# For each uncovered class r_30, we want to find a modulus d (multiple of 30, or anything)
# and a residue r % d such that r % 30 == r_30, and a linear formula k = c*m + e (for n = d*m + r)
# that works for all m.
# Actually, n doesn't have to be a multiple of 30, d can be anything. We just need to cover
# all possible residues modulo some d.
# Let's try to cover all 18 classes by finding rules for various n.
# Specifically, we want to partition each uncovered class into sub-classes modulo some d
# such that each sub-class has an algebraic rule.
# For example, class 7 % 30 can be split modulo 42 (7 % 42), modulo 70 (7 % 70), modulo 84 (7 % 84), etc.
# Wait, can we just find a set of rules that cover all numbers?
# Let's search for any rule of the form:
# n = d*m + r, k = c*m + e
# such that:
# 1. c*m + e < (d*m+r)/2 for all m >= 1
# 2. totient(k) * totient(n-k) is a square for all m >= 1.
# Let's test d up to 300.

rules = []
covered_classes = {u: [] for u in uncovered}

# We can search for d up to 210, and see which residues r % d work.
for d in [30, 42, 60, 70, 84, 90, 105, 120, 140, 150, 180, 210]:
    for r in range(d):
        r_30 = r % 30
        if r_30 not in uncovered:
            continue
        # Search for c, e
        for c in range(1, d // 2 + 1):
            # We want k = c*m + e. Since we want to prove it easily,
            # we can look for c, e such that we can factor out some term.
            # Usually, k = c*m + e and n-k = (d-c)*m + (r-e).
            # We want c*m+e and (d-c)*m+(r-e) to have a common factor or some specific form.
            # Let's just check if it works for m in [1, 20]
            for e in range(-15, 16):
                works = True
                for m in range(1, 30):
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
                    print(f"FOUND RULE: n % {d} == {r} (maps to {r_30} % 30), k = {c}*m + ({e})")
                    rules.append((d, r, r_30, c, e))
                    if r not in covered_classes[r_30]:
                        covered_classes[r_30].append(r)
