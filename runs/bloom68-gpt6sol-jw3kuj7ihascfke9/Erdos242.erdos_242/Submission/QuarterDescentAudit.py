#!/usr/bin/env python3
"""Independent exact-arithmetic audit of QuarterDescent.lean (not a proof of ESC)."""

from fractions import Fraction
from math import isqrt


def prime(n):
    return n > 1 and all(n % r for r in range(2, isqrt(n) + 1))


def square_divisors(x):
    n, factors = x, []
    for r in range(2, isqrt(x) + 1):
        if n % r == 0:
            e = 0
            while n % r == 0:
                n //= r
                e += 1
            factors.append((r, e))
    if n > 1:
        factors.append((n, 1))
    ds = [1]
    for r, e in factors:
        ds = [d * r**j for d in ds for j in range(2 * e + 1)]
    assert len(ds) == len(set(ds))
    return sorted(ds)


def check(n, triple):
    x, y, z = triple
    assert 0 < x < y < z
    assert sum((Fraction(1, t) for t in triple), Fraction(0)) == Fraction(4, n)
    return triple


def type_ii(n, x, d):
    a = 4 * x - n
    assert a > 0 and 2 * x < n and 0 < d < x and x * x % d == 0
    assert (x + d) % a == 0
    b = x * x // d
    assert (x + b) % a == 0
    return check(n, (x, n * ((x + d) // a), n * ((x + b) // a)))


def type_i(n, x, c):
    a = 4 * x - n
    assert a > 0 and 2 * x < n and c > 0 and x * x % c == 0
    assert (4 * c + 1) % a == 0
    d = x * x // c
    assert (n * x + d) % a == (n * x + n * n * c) % a == 0
    return check(n, (x, (n * x + d) // a, (n * x + n * n * c) // a))


def quarter_compatible(q, s):
    if not (q < 4 * s and 2 * s < q):
        return False
    a = 4 * s - q
    b = 4 * a + 3
    for e in square_divisors(s):
        if (4 * e + 1) % a == 0:
            m = (4 * e + 1) // a
            if 3 * (m + 1) % b == 0:
                return True
        if e < s and (s + e) % a == 0:
            m = (s + e) // a
            if 3 * (m + e) % b == 0:
                return True
    return False


def main():
    assert all(prime(n) for n in (97, 313, 631, 1303, 2521, 5209, 16633, 66529))
    assert 5209 % 840 == 169 and 5209 % 11 == 6
    assert 5209 + 4 == 13 * 401 and prime(13) and prime(401)
    q, p, s, a, d, m = 1303, 5209, 327, 5, 3, 66
    assert q + a == 4 * s and 4 * q - 3 == p and s + d == a * m
    assert (4 * a + 3) * m == (4 * s + d) + 3 * (m + d)
    assert 3 * (m + d) % (4 * a + 3) == 0
    assert type_ii(q, s, d) == (327, 85998, 9373782)
    assert type_ii(p, 4 * s, d) == (1308, 296913, 129454068)

    q, p, s, a, c, m = 16633, 66529, 4160, 7, 1300, 743
    assert q + a == 4 * s and 4 * q - 3 == p and 4 * c + 1 == a * m
    assert (4 * a + 3) * m == 4 * (4 * c) + 1 + 3 * (m + 1)
    assert 3 * (m + 1) % (4 * a + 3) == 0
    assert type_i(q, s, c) == (4160, 9886656, 51388984140)
    assert type_i(p, 4 * s, 4 * c) == (16640, 35712768, 742479606960)

    q, p = 25, 97
    assert check(q, (7, 60, 2100))
    assert type_ii(p, 28, 2) == (28, 194, 2716)
    assert 56 in square_divisors(28) and (4 * 56 + 1) % (4 * 28 - p) == 0
    assert all(not quarter_compatible(q, s) for s in range(7, 13))
    assert all((4 * e + 1) % 3 != 0 and (7 + e) % 3 != 0
               for e in square_divisors(7))

    q, p = 631, 2521
    assert type_ii(q, 158, 1)
    assert 3 * (159 + 1) % 7 != 0
    assert {e % 7 for e in square_divisors(632)} == {1, 2, 4}
    assert all((4 * e + 1) % 7 and (632 + e) % 7
               for e in square_divisors(632))
    assert type_ii(p, 636, 8) == (636, 70588, 5611746)
    print("Verified positive lifts, strict rational identities, p=97 noncoverage, and p=2521 failed fiber.")


if __name__ == "__main__":
    main()
