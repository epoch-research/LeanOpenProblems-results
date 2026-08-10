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

# Test moduli d
moduli = [12, 18, 20, 30, 42, 60, 70, 84, 105, 210]
for d in moduli:
    print(f"Checking modulus {d}...")
    for r in range(d):
        # We search for linear formula k = c*m + e, where n = d*m + r
        # Since n = d*m + r, k must satisfy 1 <= k < n/2 for all m.
        # So c must be such that 1 <= c*m + e < (d*m+r)/2. This means c < d/2.
        for c in range(1, d // 2 + 1):
            if math.gcd(c, d) != 1 and c != 1:
                # We can relax this, but coprime is easier to prove
                pass
            for e in range(-10, 11):
                works = True
                # test for a range of m
                for m in range(2, 20):
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
                    print(f"FOUND: n % {d} == {r}, k = {c}*m + ({e})")
