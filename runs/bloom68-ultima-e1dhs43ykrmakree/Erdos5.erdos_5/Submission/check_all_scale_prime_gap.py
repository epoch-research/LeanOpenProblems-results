#!/usr/bin/env python3
"""Exact arithmetic checks for AllScalePrimeGapAttempt.md.

This does NOT search for a prime-gap counterexample and does NOT prove an
asymptotic statement. It checks the finite identities and endpoint conventions
used in the written proofs. No third-party packages or Lean declarations used.
"""
from fractions import Fraction
from math import comb, gcd, isqrt


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def prime_list(limit):
    return [n for n in range(2, limit + 1) if is_prime(n)]


def least_prime_factor(n):
    assert n >= 2
    for d in range(2, isqrt(n) + 1):
        if n % d == 0:
            return d
    return n


def largest_prime_factor(n):
    assert n >= 2
    largest = 1
    while n > 1:
        p = least_prime_factor(n)
        largest = max(largest, p)
        while n % p == 0:
            n //= p
    return largest


def open_integer_interval(a, b):
    """Integers strictly between two positive Fractions."""
    lo = a.numerator // a.denominator + 1
    hi = (b.numerator - 1) // b.denominator
    return range(lo, hi + 1)


def check_elementary_index_bound():
    ps = prime_list(240)
    for m in range(1, 121):
        c = comb(2 * m, m)
        assert c * (2 * m + 1) >= 4**m
        product = 1
        for p in ps:
            if p > 2 * m:
                break
            power, exponent, terms = p, 0, 0
            while power <= 2 * m:
                summand = (2 * m) // power - 2 * (m // power)
                assert summand in (0, 1)
                exponent += summand
                terms += 1
                power *= p
            assert exponent <= terms and p**exponent <= 2 * m
            product *= p**exponent
        assert product == c
        assert c <= (2 * m) ** sum(p <= 2 * m for p in ps)
    return 120


def check_reciprocal_rows():
    cases = occupied = 0
    example = None
    simultaneous_rows = {}
    simultaneous_lower_bounds = {}
    for q, qnext in ((23, 29), (89, 97), (113, 127)):
        assert is_prime(q) and is_prime(qnext)
        assert not any(is_prime(t) for t in range(q + 1, qnext))
        u, v = q + 1, qnext - 1
        assert u < v
        for Y in (10000, 100000, 123457):
            for H in (1, 5, 17, 100):
                lo, hi = Fraction(Y + H, v), Fraction(Y, u)
                length = Fraction(Y * (v - u) - H * u, u * v)
                assert hi - lo == length
                rows = list(open_integer_interval(lo, hi))
                assert len(rows) >= length - 1
                key = (Y, H)
                previous = simultaneous_rows.setdefault(key, set())
                assert previous.isdisjoint(rows)
                previous.update(rows)
                total_lower_bound = simultaneous_lower_bounds.get(key, Fraction(0))
                total_lower_bound += max(Fraction(0), length - 1)
                simultaneous_lower_bounds[key] = total_lower_bound
                assert len(previous) >= total_lower_bound
                entries = 0
                for r in rows:
                    assert r >= 2
                    for n in range(Y, Y + H + 1):
                        assert u < Fraction(n, r) < v
                        if n % r == 0:
                            t = n // r
                            assert not is_prime(t)
                            ell = least_prime_factor(t)
                            new_r = r * (t // ell)
                            assert ell * new_r == n
                            assert new_r > r and is_prime(ell)
                            assert ell < u
                            entries += 1
                occupied += entries
                cases += 1
                if (q, qnext, Y, H) == (113, 127, 100000, 100):
                    example = (len(rows), entries, str(length))
    return cases, occupied, example


def check_uniform_sieve_and_smooth_bounds():
    cases = 0
    M = 30
    phi = sum(gcd(n, M) == 1 for n in range(M))
    assert phi == 8
    for Y in (1000, 10000, 50000):
        for H in (7, 31, 101):
            for R in (3, 5, 7):
                assert Y > 5 * (R - 1)
                exceptional = set()
                for r in range(1, R):
                    exceptional.update(
                        n for n in range(Y, Y + H + 1)
                        if n % r == 0 and is_prime(n // r)
                    )
                bound = Fraction(H * phi, M) * sum(
                    (Fraction(1, r) for r in range(1, R)), Fraction(0)
                ) + (R - 1) * phi
                assert len(exceptional) <= bound
                cases += 1
    S = (2, 3, 5)
    for Y in (10000, 50000, 100000):
        for H in (3, 7, 13):
            assert H ** len(S) < Y
            powers = []
            for p in S:
                power = 1
                while power ** len(S) < Y:
                    power *= p
                assert power > H
                powers.append(power)
            smooth = []
            for n in range(Y, Y + H + 1):
                reduced = n
                for p in S:
                    while reduced % p == 0:
                        reduced //= p
                if reduced == 1:
                    assert any(n % power == 0 for power in powers)
                    smooth.append(n)
            assert len(smooth) <= len(S)
            cases += 1
    return cases


def check_mixed_row_determinants():
    cases = 0
    # These variables need not be prime: the lemma is an integer identity.
    for q in range(2, 61):
        for qp in range(q + 1, q + 10):
            delta = qp - q
            for r in range(2, 81):
                n = q * r
                s0 = n // qp
                for s in (s0 - 1, s0, s0 + 1):
                    if s < 2:
                        continue
                    np = qp * s
                    H = abs(n - np)
                    if H > 30:
                        continue
                    Y = min(n, np)
                    assert q * qp * (r - s) == n * qp - np * q
                    if r != s:
                        assert q * (q - H) <= (Y + H) * delta
                        if q > H:
                            assert r > s
                    else:
                        assert H == r * delta
                    cases += 1
    return cases


def check_euclidean_near_collisions():
    ps = prime_list(5000)
    cases = 0
    example = None
    for q, qp in zip(ps, ps[1:]):
        delta = qp - q
        if delta <= 2 or 2 * delta >= q:
            continue
        s = (2 * q) // delta
        if s % 2 == 0:
            s -= 1
        r = s + 2
        d = 2 * q - s * delta
        x, y = q * r, qp * s
        assert 3 <= s < r < q
        assert s % 2 == r % 2 == 1
        assert x - y == d and 0 < d < 2 * delta and d % 2 == 0
        assert not is_prime(x) and not is_prime(y)
        assert largest_prime_factor(x) == q
        assert largest_prime_factor(y) == qp
        main_height = Fraction(2 * q * q, delta)
        assert main_height < x <= main_height + 2 * q
        assert main_height - 2 * delta < y <= main_height + 2 * q
        assert q * (q - d) <= x * delta
        cases += 1
        if (q, qp) == (23, 29):
            example = dict(q=q, qnext=qp, s=s, r=r, x=x, y=y, d=d)
    return cases, example


def main():
    print('Elementary binomial/index checks:', check_elementary_index_bound())
    cases, occupied, example = check_reciprocal_rows()
    print('Reciprocal row cases:', cases, '; occupied entries refined:', occupied)
    print('Row example (excluded rows, occupied entries, interval length):', example)
    print('Uniform sieve/smooth cases:', check_uniform_sieve_and_smooth_bounds())
    print('Exact mixed-row determinant cases:', check_mixed_row_determinants())
    cases, example = check_euclidean_near_collisions()
    print('Euclidean identities on consecutive-prime inputs:', cases)
    print('Illustrative identity:', example)
    print('PASS: all exact checks; no asymptotic or prime-gap conjecture claimed.')


if __name__ == '__main__':
    main()
