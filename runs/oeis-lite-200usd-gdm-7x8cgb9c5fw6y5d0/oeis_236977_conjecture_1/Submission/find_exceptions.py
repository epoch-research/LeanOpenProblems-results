import math

def totient(n):
    # simple totient for analysis
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

def has_algebraic_rule(n):
    if n % 6 == 3:
        return True
    if n % 10 == 0:
        return True
    if n % 6 == 0: # since n % 10 == 0 is already checked, this covers all n % 6 == 0
        return True
    return False

# Let's count how many numbers are not covered
uncovered = 0
for n in range(9, 2000000 + 1):
    if not has_algebraic_rule(n):
        uncovered += 1

print(f"Total uncovered: {uncovered}")
