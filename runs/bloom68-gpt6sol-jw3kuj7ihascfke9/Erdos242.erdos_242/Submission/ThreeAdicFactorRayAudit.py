"""Independent exact audit of the finite claims in ThreeAdicFactorRay.lean.

No outside libraries; this is NOT a search for or certification of a bad prime.
"""
from fractions import Fraction
from math import isqrt


def factors(n):
    assert n > 0
    result = {}
    q = 2
    while q * q <= n:
        while n % q == 0:
            result[q] = result.get(q, 0) + 1
            n //= q
        q += 1
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result


def divisors(n):
    out = [1]
    for q, e in factors(n).items():
        out = [a * q**i for a in out for i in range(e + 1)]
    return sorted(out)


def root_radical(d):
    # rho(d) is the least integer whose square is divisible by d.
    result = 1
    for q, e in factors(d).items():
        result *= q**((e + 1) // 2)
    return result


p = 241
assert all(p % q for q in range(2, isqrt(p) + 1)) and p % 24 == 1
count = 0
for d in range(2, (p - 1) // 4 + 1, 3):
    assert 4 * d < p and d % 3 == 2
    n = p + 4 * d
    assert n % 3 == 0
    # Exact factor-ray equivalence: d|m² and h=4m-1 iff h=-1 mod 4*rho(d).
    ray = 4 * root_radical(d)
    assert not any(h > 1 and (h + 1) % ray == 0 for h in divisors(n))
    count += 1
assert count == 20
assert factors(p + 4 * 2).get(3) == 1
assert factors(p + 4 * 8).get(3) == 1

for a in (3, 27):
    assert a < p and a % 4 == 3
    x = (p + a) // 4
    assert 4 * x - p == a and x in (61, 67)
    sq_divs = divisors(x * x)
    assert not any((4 * c + 1) % a == 0 for c in sq_divs)  # full Type I
    assert not any(d < x and (x + d) % a == 0 for d in sq_divs)  # full Type II

x, a, d, c = 62, 7, 1, 124
assert d in divisors(x * x) and d < x and (x + d) % a == 0
assert c in divisors(x * x) and (4 * c + 1) % a == 0
Y = p * (x + d) // a
Z = p * (x + x*x // d) // a
assert (x, Y, Z) == (62, 2169, 134478)
assert x < Y < Z and Fraction(4, p) == sum((Fraction(1, n) for n in (x, Y, Z)))
print(f"Verified p={p}: all {count} d≡2 (mod 3) with 4d<p miss full Type II;")
print("both pure-3-power first-denominator fibers fail both types;")
print(f"ordered Type II triple {(x, Y, Z)} and full Type I witness c={c} succeed.")
