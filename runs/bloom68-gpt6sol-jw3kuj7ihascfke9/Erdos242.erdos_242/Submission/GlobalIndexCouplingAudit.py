#!/usr/bin/env python3
"""Exact standard-library audit of the partial results in GlobalIndexCoupling.md.

Factors and primalities are checked by trial division, all square divisors
are generated from full prime-exponent ranges, and fractions use Fraction.
This is a finite audit, NOT a proof of the universal Erdős–Straus assertion.
"""

from fractions import Fraction
from math import gcd


def factor(n):
    assert n > 0
    result = []
    q = 2
    while q * q <= n:
        if n % q == 0:
            exponent = 0
            while n % q == 0:
                n //= q
                exponent += 1
            result.append((q, exponent))
        q = 3 if q == 2 else q + 2
    if n > 1:
        result.append((n, 1))
    return result


def is_prime(n):
    return n >= 2 and factor(n) == [(n, 1)]


def square_divisors(n):
    out = [1]
    for q, e in factor(n):
        out = [d * q**i for d in out for i in range(2 * e + 1)]
    assert len(out) == len(set(out))
    assert all(n * n % d == 0 for d in out)
    return sorted(out)


def rho(t):
    out = 1
    for q, e in factor(t):
        out *= q ** ((e + 1) // 2)
    return out


def test_certificates(p, x, a, i_certificates, ii_certificates):
    assert 4 * x == p + a and 0 < a < p and p < 4 * x and 2 * x < p
    for c in i_certificates:
        assert c > 0 and x * x % c == 0 and (4 * c + 1) % a == 0
        r = x * x // c
        assert (p * x + r) % a == 0 and (p * x + p * p * c) % a == 0
        y = (p * x + r) // a
        z = (p * x + p * p * c) // a
        assert 0 < x < y < z
        assert Fraction(4, p) == Fraction(1, x) + Fraction(1, y) + Fraction(1, z)
    for d in ii_certificates:
        assert 0 < d < x and x * x % d == 0 and (x + d) % a == 0
        e = x * x // d
        assert (x + e) % a == 0
        y = p * (x + d) // a
        z = p * (x + e) // a
        assert 0 < x < y < z
        assert Fraction(4, p) == Fraction(1, x) + Fraction(1, y) + Fraction(1, z)


def stress_primes():
    tests = [
        (193, 1, [5, 250], [20]),
        (2521, 5, [477], [8]),
        (66529, 4, [2179447], []),
        (1915201, 11, [239406], [24]),
    ]
    for p, first, expected_i, expected_ii in tests:
        assert is_prime(p) and (p - 1) % 24 == 0
        k = (p - 1) // 24
        q = 6 * k + 1
        assert first < 6 * k
        for j in range(first + 1):
            x = q + j
            a = 4 * j + 3
            all_ds = square_divisors(x)
            i_hits = [t for t in all_ds if (4 * t + 1) % a == 0]
            ii_hits = [t for t in all_ds if t < x and (x + t) % a == 0]
            if j < first:
                assert i_hits == ii_hits == []
            else:
                assert i_hits == expected_i and ii_hits == expected_ii
                test_certificates(p, x, a, i_hits, ii_hits)
        print(f"p={p}: all j<{first} fail; j={first}, x={q+first}, "
              f"I={expected_i}, II={expected_ii}")

    p, q = 1915201, (1915201 + 3) // 4
    for j in range(11):
        x = q + j
        a = 4 * j + 3
        residues = {t % a for t in square_divisors(x)}
        # Both targets are absent even BEFORE the Type-II size bound.
        assert -pow(4, -1, a) % a not in residues
        assert -x % a not in residues
    print("p=1915201: both exact targets miss all square-divisor residues at j=0,...,10")


def retained_edge(p, source_j, target_j, t):
    k = (p - 1) // 24
    q = 6 * k + 1
    assert 0 <= source_j < 6 * k and 0 <= target_j < 6 * k
    x = q + source_j
    X = q + target_j
    A = 4 * target_j + 3
    if x * x % t or X * X % t:
        return False
    return (4 * t + 1) % A == 0 or (p + 4 * t) % A == 0


def isolated_initial_fibers():
    p = 193
    old = square_divisors(49)
    assert old == [1, 7, 49, 343, 2401]
    expected_i = [[(5, 1)], [(29, 1)], [(197, 1)],
                  [(1373, 1)], [(5, 1), (17, 1), (113, 1)]]
    expected_ii = [[(197, 1)], [(13, 1), (17, 1)], [(389, 1)],
                   [(5, 1), (313, 1)], [(97, 1), (101, 1)]]
    for t, fi, fii in zip(old, expected_i, expected_ii):
        assert factor(4 * t + 1) == fi and factor(p + 4 * t) == fii
        assert all(q % 4 == 1 and is_prime(q) for q, _ in fi + fii)

    for p in (193, 2521, 66529, 1915201):
        k = (p - 1) // 24
        q = 6 * k + 1
        old = square_divisors(q)
        if p != 193:
            assert is_prime(q)
            assert all(r % 4 == 1 for r, _ in factor(p + 4))
        assert not any(retained_edge(p, 0, j, t)
                       for j in range(1, 6 * k) for t in old)
        print(f"p={p}: no retained-divisor edge from failed j=0 to ANY later j")

    # A real failed-to-success edge, requiring 8 | 636^2 but 8 NOT | 636.
    p, j, J, d = 2521, 1, 5, 8
    x, X = (p + 3) // 4 + j, (p + 3) // 4 + J
    assert x == 632 and X == 636 and rho(d) == 4 and (J - j) % rho(d) == 0
    assert retained_edge(p, j, J, d) and (p + 4 * d) % (4 * J + 3) == 0
    assert X * X % d == 0 and X % d != 0 and X + d == 644
    print("p=2521: genuine failed j=1 -> successful j=5, retaining d=8")

    assert rho(127 * 131**2) == 16637 > 4
    assert rho(239406) == 239406 > 11 and rho(24) == 12 > 11
    print("p=66529 and 1915201: first-success divisors cannot be retained "
          "from any earlier failed index")


def two_index_duality():
    a, r, h, p = 7, 19, 63, 8353
    assert is_prime(p) and p % 24 == 1 and p == a * h * r - a - r
    u = (a * h - 1) // 4
    v = (r * h - 1) // 4
    assert u == 110 and v == 299 and h * p + 1 == 16 * u * v
    triples = [(r * u, 4 * r * u * v, 4 * p * u * v),
               (a * v, 4 * a * u * v, 4 * p * u * v)]
    assert triples == [(2090, 2499640, 1098920680),
                       (2093, 920920, 1098920680)]
    for x, y, z in triples:
        assert p < 4 * x and 2 * x < p and 0 < x < y < z
        assert Fraction(4, p) == Fraction(1, x) + Fraction(1, y) + Fraction(1, z)
    assert gcd(3192, 1969) == 1
    print("p=8353: simultaneous j=1,j=4 Type-I solutions with a common last denominator")


if __name__ == "__main__":
    stress_primes()
    isolated_initial_fibers()
    two_index_duality()
    print("PASS: all tests finite/conditional; universal hard-prime cover remains open")
