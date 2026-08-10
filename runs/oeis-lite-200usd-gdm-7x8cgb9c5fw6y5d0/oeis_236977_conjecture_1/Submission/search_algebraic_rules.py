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

# We want to test if for a given d and r, there is some constant fraction c/d (with gcd(c, d) = 1)
# such that k = c * (n / d) is a witness for all n = d * m + r.
# Or more generally, we want to check if for all n in a residue class n % d == r,
# a specific witness formula k(n) works.

# Let's test d up to 60.
for d in [6, 10, 12, 14, 15, 18, 20, 30]:
    for r in range(d):
        # We want to find a formula k = c * m + e for n = d * m + r
        # such that phi(k) * phi(n-k) is a square for all m.
        # Since phi(k) * phi(n-k) must be square, we can test for m up to 20.
        # Let's search over possible linear formulas k = c * m + e
        # where 1 <= k < n/2.
        for c in range(1, d // 2 + 1):
            for e in range(-5, 6):
                # Check if this k works for all m in [2, 30]
                works = True
                for m in range(2, 30):
                    n = d * m + r
                    k = c * m + e
                    if not (1 <= k < (n - 1) // 2 + 1):
                        works = False
                        break
                    prod = totient(k) * totient(n - k)
                    if not is_square(prod):
                        works = False
                        break
                if works:
                    print(f"FOUND RULE: for n % {d} == {r} (n = {d}*m + {r}), k = {c}*m + {e} is a witness!")
