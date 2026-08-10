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
for c in range(2, 2000):
    if is_square(totient(c)):
        good_c.append(c)

print(f"Good c values: {good_c[:30]} ... (total {len(good_c)})")

def has_algebraic_rule(n):
    if n % 6 == 3:
        return True
    if n % 10 == 0:
        return True
    if n % 6 == 0:
        return True
    
    # Try rule_coprime with various c
    for c in good_c:
        if n % (c + 1) == 0:
            k = n // (c + 1)
            # check Coprime c k
            if math.gcd(c, k) == 1:
                return True
    return False

# Count how many of a small sample (e.g., up to 100,000) are uncovered
uncovered = 0
sample_limit = 100000
for n in range(9, sample_limit + 1):
    if not has_algebraic_rule(n):
        uncovered += 1

print(f"Uncovered up to {sample_limit}: {uncovered} ({(uncovered/sample_limit)*100:.2f}%)")
