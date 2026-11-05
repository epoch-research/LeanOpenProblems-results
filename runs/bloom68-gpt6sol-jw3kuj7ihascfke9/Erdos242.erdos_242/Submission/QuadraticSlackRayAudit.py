"""Independent exact finite audit for QuadraticSlackRay.md (standard library only).

This does NOT prove that the conditional norm-coordinate factor condition
holds for every hard prime, nor that any prime is an ESC counterexample.
"""

from fractions import Fraction
from math import isqrt


def prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def ordered_factors(p: int, q: int) -> list[tuple[int, int]]:
    """Every a<p, a,b≡3 (mod 4) with ab=p²+4q, no primality shortcut."""
    N = p * p + 4 * q
    return [
        (a, N // a)
        for a in range(1, p)
        if N % a == 0 and a % 4 == 3 and (N // a) % 4 == 3
    ]


cases = [
    (73, 5, 4, 5, [(3, 1783)], []),
    (97, 7, 4, 7, [], []),
    (1249, 7, 20, 7, [(739, 2111)], [(739, 2111)]),
]

for p, u, v, q, expected_factors, expected_hits in cases:
    assert prime(p) and prime(q)
    assert p % 24 == 1 and p == u * u + 3 * v * v
    assert q < p and u % q == 0 and q % 12 in (5, 7)
    assert pow(q, (p - 1) // 2, p) == p - 1  # (q/p)=-1
    N = p * p + 4 * q
    factors = ordered_factors(p, q)
    hits = [(a, b) for a, b in factors if (p + a) % (4 * q) == 0]
    assert factors == expected_factors and hits == expected_hits
    for a, b in factors:
        assert 0 < a < p < b and a * b == N
        x, y = (p + a) // 4, (p + b) // 4
        assert x < y and p < 4 * x < 2 * p
        # Check necessity as well as sufficiency of the ray condition.
        assert ((x * y) % q == 0) == ((p + a) % (4 * q) == 0)
    for a, b in hits:
        t = (p + a) // (4 * q)
        x, y = q * t, (p + b) // 4
        z = p * t * y
        c = q * t * t
        assert 0 < x < y < z
        assert p < 4 * x and 2 * x < p
        assert a == 4 * x - p and x * x == q * c
        assert (4 * c + 1) % a == 0
        assert 4 * x * y == p * (x + y) + q
        assert Fraction(4, p) == Fraction(1, x) + Fraction(1, y) + Fraction(1, z)
        print(f"p={p}: a={a}, b={b}, q={q}, c={c}, (x,y,z)=({x},{y},{z})")

# Verify both negative certificates, without relying on external factorization.
assert prime(9437) and 9437 == 97**2 + 4 * 7 and 9437 % 4 == 1
assert prime(1783) and 5349 == 73**2 + 4 * 5 == 3 * 1783
assert (73 + 3) % 20 != 0 and (19 * 464) % 5 == 1

# Verify that the success uses full Type I and is not Type II at that x.
p, x, a, q, c = 1249, 497, 739, 7, 35287
assert prime(739) and prime(2111)
assert p == 24 * 52 + 1 and x == 6 * 52 + 1 + 184 and 184 < 6 * 52
assert a == 4 * 184 + 3 and x * x == q * c and c > x
assert 4 * c + 1 == a * 191
assert [d for d in range(1, x) if (x * x) % d == 0 and (x + d) % a == 0] == []
assert [d for d in range(1, x + 1) if x % d == 0 and (4 * d + 1) % a == 0] == []
assert prime(313) and (1249 + 3) // 4 == 313
assert all(d % 3 == 1 for d in range(1, 313 * 313 + 1) if (313 * 313) % d == 0)
assert prime(29) and 4 * 7 + 1 == 29
assert not any(29 % a == 0 for a in range(3, 30, 4))  # c=7 never works directly
assert 193 == 1 * 1 + 3 * 8 * 8
assert [(isqrt(193 - 3 * v * v), v) for v in range(1, isqrt(193 // 3) + 1)
        if isqrt(193 - 3 * v * v) ** 2 + 3 * v * v == 193] == [(1, 8)]
# The only positive norm coordinate u=1 has no prime factor q.

# Each "failure" is a failure only of A=q, not of Erdős–Straus.
for p, (x, y, z) in [
    (97, (25, 970, 4850)),
    (73, (20, 220, 4015)),
]:
    assert 0 < x < y < z
    assert Fraction(4, p) == Fraction(1, x) + Fraction(1, y) + Fraction(1, z)

print("All finite norm-coordinate, factor-ray and ordered-fraction checks passed.")
