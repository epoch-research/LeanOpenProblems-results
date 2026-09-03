#!/usr/bin/env python3
"""Exact finite algebra checks for CenteredCompositeTransportAudit.md.

Standard library only.  No floating-point spectral or prime-pair inference.
Run from any directory with: python3 Submission/check_centered_composite_transport.py
"""

from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from hashlib import sha256
from itertools import combinations
from math import isqrt, prod
from pathlib import Path
from random import Random


@lru_cache(None)
def primes_up_to(limit):
    return tuple(n for n in range(2, limit + 1)
                 if all(n % d for d in range(2, isqrt(n) + 1)))


@lru_cache(None)
def factor(n):
    assert n >= 1
    out = []
    p = 2
    while p * p <= n:
        exponent = 0
        while n % p == 0:
            n //= p
            exponent += 1
        if exponent:
            out.append((p, exponent))
        p += 1
    if n > 1:
        out.append((n, 1))
    return tuple(out)


def omega(n):
    return sum(exponent for _, exponent in factor(n))


@lru_cache(None)
def products(pool, degree):
    if degree < 0:
        return ()
    return tuple(prod(labels) for labels in combinations(pool, degree))


def squarefree_divisors(m):
    labels = tuple(p for p, exponent in factor(m))
    assert all(exponent == 1 for _, exponent in factor(m))
    return tuple(d for j in range(len(labels) + 1) for d in products(labels, j))


def divisors(n):
    return tuple(d for d in range(1, n + 1) if n % d == 0)


@lru_cache(None)
def center_residue(m, residue):
    return prod((Q(int(residue % p == 0)) - Q(1, p)
                 for p, exponent in factor(m)), start=Q(1))


def center(m, n):
    return center_residue(m, n % m)


def phi_ratio(m):
    return prod((1 - Q(1, p) for p, exponent in factor(m)), start=Q(1))


def harmonic(pool, degree):
    return sum((Q(1, m) for m in products(pool, degree)), Q(0))


@lru_cache(None)
def small_part(n, y):
    assert n >= 1
    s, r, degree = 1, n, 0
    for p in primes_up_to(y):
        while r % p == 0:
            s *= p
            r //= p
            degree += 1
    return s, r, degree


def a(r):
    return 2 + r % 5


def b(r):
    return (1 + r % 7) * (-1) ** omega(r)


def lift(n, y, z, mark):
    s, r, degree = small_part(n, y)
    return z ** degree * mark(r)


def masked_transport():
    pool, y, N = (3, 5, 7), 11, 1000
    z, w = Q(2, 3), Q(3, 5)
    X = {n for n in range(N + 1, 2 * N + 1)
         if n % 13 not in (0, 5) and n not in (N + 1, 2 * N - 1)}
    cases = ((1, 2), (2, 2), (2, 4), (3, 2), (3, 4), (2, 6), (3, 6))
    nonzero_diagonals = 0
    for k, h in cases:
        direct = direct_bicoeff = direct_onecoeff = direct_diag = Q(0)
        expanded = expanded_bicoeff = expanded_onecoeff = Q(0)
        diagonal = Q(0)
        for m in products(pool, k):
            for n in sorted(X):
                sn, rn, dn = small_part(n, y)
                for sigma in (-1, 1):
                    end = n + sigma * h * m
                    if end not in X:
                        continue
                    assert center(m, n) == center(m, end)
                    se, re, de = small_part(end, y)
                    base = Q(a(rn) * b(re))
                    direct += center(m, n) * z ** dn * w ** de * base
                    if dn == de == k:
                        direct_bicoeff += center(m, n) * base
                    if dn + de == 2 * k:
                        direct_onecoeff += center(m, n) * base
                    if sn == se == m:
                        direct_diag += center(m, n) * base

            for d in squarefree_divisors(m):
                e, j = m // d, omega(d)
                signed = Q((-1) ** omega(e), e)
                for u in range(N // d + 1, 2 * N // d + 1):
                    if d * u not in X:
                        continue
                    _, ru, du = small_part(u, y)
                    for sigma in (-1, 1):
                        end = u + sigma * h * e
                        if d * end not in X:
                            continue
                        _, re, de = small_part(end, y)
                        base = Q(a(ru) * b(re))
                        expanded += signed * (z * w) ** j * z ** du * w ** de * base
                        if du == de == k - j:
                            expanded_bicoeff += signed * base
                        if du + de == 2 * (k - j):
                            expanded_onecoeff += signed * base

            # The common-smooth-part m component, with the exact masks.
            for r in range(N // m + 1, 2 * N // m + 1):
                if small_part(r, y)[0] != 1 or m * r not in X:
                    continue
                for sigma in (-1, 1):
                    end = r + sigma * h
                    if m * end not in X or small_part(end, y)[0] != 1:
                        continue
                    diagonal += phi_ratio(m) * a(r) * b(end)

        assert direct == expanded, (k, h, "transport")
        assert direct_bicoeff == expanded_bicoeff, (k, h, "bivariate coefficient")
        assert direct_onecoeff == expanded_onecoeff, (k, h, "single-variable coefficient")
        assert direct_diag == diagonal, (k, h, "short-shift diagonal")
        nonzero_diagonals += bool(diagonal)
    assert nonzero_diagonals >= 3
    print(f"PASS masked transport, both coefficient extractions, diagonal: {len(cases)} cases")


def triangular_inversion():
    pool = (3, 5, 7, 11)
    patterns = 0
    for k in range(1, len(pool) + 1):
        for m in products(pool, k):
            ds = squarefree_divisors(m)
            assert sum((Q((-1) ** omega(m // d), m // d) for d in ds), Q(0)) == phi_ratio(m)
            for n in range(m):
                forward = sum((Q((-1) ** omega(m // d), m // d) * int(n % d == 0)
                               for d in ds), Q(0))
                backward = sum((center(d, n) / (m // d) for d in ds), Q(0))
                assert forward == center(m, n)
                assert backward == int(n % m == 0)
                assert sum((center(d, n) / (m // d) for d in ds if d != 1), Q(0)) == Q(int(n % m == 0)) - Q(1, m)
                patterns += 1
    print(f"PASS Boolean-lattice inversion: {patterns} residue patterns")


def crt_polynomials():
    pool, h, x = (3, 5, 7, 11), 2, Q(1, 2)
    period = prod(pool)
    degrees = range(len(pool) + 1)
    labels = {j: products(pool, j) for j in degrees}
    variances = {p: Q(1, p) * (1 - Q(1, p)) for p in pool}
    W = {j: sum((prod((variances[p] for p, _ in factor(m)), start=Q(1))
                 for m in labels[j]), Q(0)) for j in degrees}
    S = {j: [sum((center(m, n) for m in labels[j]), Q(0))
             for n in range(period)] for j in degrees}

    def mean_product(f, g):
        return sum((u * v for u, v in zip(f, g)), Q(0)) / period

    def apply(k, f):
        # A periodic CRT reference average, not a finite-interval norm assertion.
        return [sum((center(m, n) * f[(n + sigma * h * m) % period]
                     for m in labels[k] for sigma in (-1, 1)), Q(0))
                for n in range(period)]

    for i in degrees:
        for j in degrees:
            assert mean_product(S[i], S[j]) == (W[j] if i == j else 0)
    partition_cases = 0
    nonzero_remainders = 0
    for k in range(1, len(pool) + 1):
        for i in range(k + 1):
            j = k - i
            choose = len(tuple(combinations(range(k), i)))
            assert mean_product(S[i], apply(k, S[j])) == 2 * choose * W[k]
            partition_cases += 1
        T = [sum((x ** j * S[j][n] for j in range(k + 1)), Q(0))
             for n in range(period)]
        norm = mean_product(T, T)
        assert norm == sum((x ** (2 * j) * W[j] for j in range(k + 1)), Q(0))
        assert norm <= prod((1 + x * x * variances[p] for p in pool), start=Q(1))
        actual = mean_product(T, apply(k, T))
        inside = 2 * sum((prod((variances[p] * (2 * x + x * x * (1 - Q(2, p)))
                                for p, _ in factor(m)), start=Q(1))
                          for m in labels[k]), Q(0))
        remainder_factor = prod((1 + x * x / (p * p) for p in pool), start=Q(1)) - 1
        assert abs(actual - inside) <= inside * remainder_factor
        nonzero_remainders += actual != inside
    assert nonzero_remainders > 0
    print(f"PASS CRT orthogonality, {partition_cases} partition moments, 4 truncated count tests")


def pinched_blocks():
    pool, y, N, k = (5, 7, 11), 13, 1600, 2
    X = {n for n in range(N + 1, 2 * N + 1) if n % 17 not in (0, 6)}
    summary = []
    for h in (2, 4, 6):
        assert all(h % p for p in pool)
        direct, predicted = defaultdict(Q), defaultdict(Q)
        for n in sorted(X):
            sn, rn, dn = small_part(n, y)
            if dn != k:
                continue
            for m in products(pool, k):
                for sigma in (-1, 1):
                    end = n + sigma * h * m
                    if end in X and small_part(end, y)[0] == sn:
                        direct[n, end] += center(m, n)

        block_parameters = {}
        for v in divisors(h):
            ell = omega(v)
            if ell > k:
                continue
            for d in products(pool, k - ell):
                s = d * v
                rest = tuple(p for p in pool if d % p)
                bound = 2 * phi_ratio(d) * harmonic(rest, ell)
                block_parameters[s] = d, v, ell, bound
                for r in range(N // s + 1, 2 * N // s + 1):
                    n = s * r
                    if n not in X or small_part(r, y)[0] != 1:
                        continue
                    for e in products(rest, ell):
                        for sigma in (-1, 1):
                            end_r = r + sigma * (h // v) * e
                            end = s * end_r
                            if end not in X or small_part(end_r, y)[0] != 1:
                                continue
                            predicted[n, end] += Q((-1) ** ell, e) * phi_ratio(d)
        assert dict(direct) == dict(predicted), (h, "pinched formula")
        rows = defaultdict(Q)
        long_edges = 0
        for (n, end), weight in direct.items():
            sn = small_part(n, y)[0]
            d, v, ell, bound = block_parameters[sn]
            rows[n] += abs(weight)
            if v == 1:
                assert abs(end - n) == h * sn
                assert weight == phi_ratio(sn)
            else:
                assert abs(end - n) // sn >= min(pool)
                long_edges += 1
            if (h // v) % 2:
                raise AssertionError("An odd shift cannot connect two y-rough cofactors")
        for n, row in rows.items():
            sn = small_part(n, y)[0]
            assert row <= block_parameters[sn][3]
            if sn in products(pool, k):
                assert row <= 2
        assert direct
        if h == 2:
            assert long_edges == 0
        else:
            assert long_edges > 0
        summary.append((h, len(direct), long_edges))
    print(f"PASS exact pinching and Schur/odd-shift checks (h, oriented edges, long): {summary}")


def signed_rows():
    pool, h, N = (3, 5, 7), 2, 1200
    V = set(range(N + 1, 2 * N + 1))
    rng = Random(271828)
    cases = 0
    for k in (1, 2, 3):
        labels = products(pool, k)
        E = harmonic(pool, k)
        M = h * max(labels)
        interior = range(N + M + 1, 2 * N - M + 1)
        rough = {n for n in interior if all(n % p for p in pool)}
        prime = {n for n in rough if factor(n) == ((n, 1),)}
        assert rough and prime
        for R in (rough, prime):
            bad_sets = [set(), set(rng.sample(sorted(V), 11)),
                        set(rng.sample(sorted(V), 90)),
                        set(sorted(R)[:max(1, len(R) // 5)])]
            for bad in bad_sets:
                X = V - bad
                retained = R & X
                rho, delta, r = Q(len(R), N), Q(len(bad), N), Q(len(retained), N)
                signed_cross = Q(0)
                loss = Q(0)
                for n in retained:
                    full_row = sum((center(m, n) for m in labels for _ in (-1, 1)), Q(0))
                    assert full_row == 2 * (-1) ** k * E
                    for m in labels:
                        for sigma in (-1, 1):
                            end = n + sigma * h * m
                            assert end in V
                            if end in X:
                                signed_cross += (-1) ** k * center(m, n) / N
                            else:
                                loss += Q(1, m * N)
                assert signed_cross == 2 * E * r - loss
                assert loss <= 2 * E * delta
                assert signed_cross >= 2 * E * (r - delta)
                if rho > 2 * delta:
                    # Square the Cauchy--Schwarz quotient to stay in exact rationals.
                    quotient_squared = (signed_cross / E) ** 2 / (r * (1 - delta))
                    assert quotient_squared >= 4 * (rho - 2 * delta) ** 2 / rho
                cases += 1
    print(f"PASS boundary-honest signed rows and arbitrary deletion inequality: {cases} cases")


def main():
    masked_transport()
    triangular_inversion()
    crt_polynomials()
    pinched_blocks()
    signed_rows()
    spec = Path(__file__).with_name("Spec.lean")
    digest = sha256(spec.read_bytes()).hexdigest()
    assert digest == "47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123"
    print(f"PASS Spec unchanged: {digest}")
    print("All exact finite checks passed; no asymptotic prime-pair claim is tested here.")


if __name__ == "__main__":
    main()
