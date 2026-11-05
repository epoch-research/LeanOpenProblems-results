"""Independent exact-integer checks for SmallShiftRigidity.md (not a proof of coverage)."""

from fractions import Fraction


def factor(n):
    assert n > 0
    result = {}
    q = 2
    while q * q <= n:
        if n % q == 0:
            exponent = 0
            while n % q == 0:
                exponent += 1
                n //= q
            result[q] = exponent
        q += 1 if q == 2 else 2
    if n > 1:
        result[n] = 1
    return result


def divisors(n, power=1):
    assert n > 0 and power > 0
    result = [1]
    for q, exponent in factor(n).items():
        result = [d * q**a for d in result for a in range(power * exponent + 1)]
    return sorted(result)


def prime(n):
    return n > 1 and len(factor(n)) == 1 and next(iter(factor(n).values())) == 1


def shifted_hits(p, r):
    """All full witnesses whose modulus divides p+r, with NO d|m shortcut."""
    return [(h, m, d)
            for h in divisors(p + r) if h % 4 == 3
            for m in [(h + 1) // 4]
            for d in divisors(m, 2)
            if 4 * d < p and (p + 4 * d) % h == 0]


CASES = [
    # p,  r,  h,    m,  d  (r is the factor shift, not necessarily 4d)
    (193,       2,  15,    4,    8),
    (2521,      2,  87,   22,   44),
    (18481,     2, 183,   46,   92),
    (1321,      2,   7,    2,    4),
    (457,       3,  23,    6,   18),
    (66529,     5,  39,   10,   50),
    (2784961,  24,  47,   12,    6),
]

for p, r, h, m, d in CASES:
    assert prime(p) and p % 24 == 1
    assert (h, m, d) in shifted_hits(p, r)
    assert h == 4 * m - 1 and p % h != 0
    assert m <= (p - 1) // 6 and m * m % d == 0 and 4 * d < p
    a = (p + 4 * d) // h
    assert (p + a) % 4 == 0
    x, y = (p + a) // 4, p * m
    assert p * m * x % d == 0
    z = p * m * x // d
    assert 0 < x < y < z
    assert Fraction(4, p) == Fraction(1, x) + Fraction(1, y) + Fraction(1, z)
    print(f"p={p}, p+{r}: h={h}, m={m}, d={d}, (x,y,z)={(x,y,z)}")

# The missing 5- or 7-mod-8 factor is a factorization assertion, not just a
# failed small-m scan; all displayed factors pass independent trial division.
for p, expected in (
    (193, {3: 1, 5: 1, 13: 1}),
    (2521, {3: 1, 29: 2}),
    (18481, {3: 1, 61: 1, 101: 1}),
    (1321, {3: 3, 7: 2}),
    (66529, {3: 1, 67: 1, 331: 1}),
    (2784961, {3: 1, 19: 1, 48859: 1}),
    (12721, {3: 1, 4241: 1}),
):
    assert prime(p) and p % 24 == 1
    actual = factor(p + 2)
    assert actual == expected and all(prime(q) for q in actual)
    factor_test = any(q % 8 in (5, 7) for q in actual)
    divisor_test = any(h % 8 == 7 for h in divisors(p + 2))
    assert factor_test == divisor_test == bool(shifted_hits(p, 2))
    print(f"p={p}, p+2 factors={actual}, full shifted witness={factor_test}")
# The p+4 factor test also has no 3-mod-4 prime factor in the hard examples.
assert prime(66533) and 66533 % 4 == 1
assert factor(2784961 + 4) == {5: 1, 293: 1, 1901: 1}
assert all(prime(q) and q % 4 == 1 for q in factor(2784961 + 4))


# Check the entire *shift* fibers (all h|p+r, all d|m², with 4d<p).
# At 2784961 the first positive shifted factor test is r=16, although
# the first full modular witness uses (m,d)=(12,6), i.e. r=24.
assert all(not shifted_hits(2784961, r) for r in range(1, 16))
assert (767, 192, 4) in shifted_hits(2784961, 16)
assert all((2784961 + 4 * d) % (4 * m - 1) != 0
           for m in range(1, 12) for d in divisors(m, 2) if 4 * d < 2784961)

assert all(not shifted_hits(66529, r) for r in range(1, 5))

# Finite consistency checks for the universal algebra proved in Lean;
# no search range is claimed to establish a universal theorem.
for m in range(1, 2001):
    h = 4 * m - 1
    for d in divisors(m, 2):
        for r in (1, 2, 3):
            if (4 * d - r) % h == 0:
                assert d == r * m and m % r == 0
        if (3 + 4 * d) % h == 0:
            assert (m, d) == (2, 1)
        if m >= 2:
            assert (2 + 4 * d) % h != 0
        for s in range(1, 6):
            assert (s * s + 4 * d) % h != 0

print("Exact fractions, factorizations, short-shift fibers and bounded sanity checks pass.")
