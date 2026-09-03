#!/usr/bin/env python3
"""Finite checks for CubeExtremalInvestigation.md; no test of the open conjecture."""
from fractions import Fraction
from itertools import combinations
from math import comb, exp, factorial, isclose, lgamma, log, log1p
from pathlib import Path
import hashlib
import random


def square_graph(edges):
    edges = set(edges)
    vertices = sorted(edges)
    aux = set()
    for i, (x, y) in enumerate(vertices):
        for j in range(i + 1, len(vertices)):
            xp, yp = vertices[j]
            if x != xp and y != yp and (x, yp) in edges and (xp, y) in edges:
                aux.add((i, j))
    return vertices, aux


def check_square_identity(a, b, edges):
    adj = [{y for x, y in edges if x == u} for u in range(a)]
    da = [len(v) for v in adj]
    db = [sum(y in v for v in adj) for y in range(b)]
    e = len(edges)
    c4 = sum(comb(len(adj[x] & adj[xp]), 2) for x, xp in combinations(range(a), 2))
    hom = sum(len(adj[x] & adj[xp]) ** 2 for x in range(a) for xp in range(a))
    assert 4 * c4 == hom - sum(v * v for v in da) - sum(v * v for v in db) + e
    vertices, aux = square_graph(edges)
    assert len(vertices) == e and len(aux) == 2 * c4
    lower = Fraction(e ** 4, 2 * a * a * b * b) - Fraction((a + b - 1) * e, 2)
    assert len(aux) >= lower
    lower2 = Fraction(8 * e ** 4, (a + b) ** 4) - Fraction((a + b - 1) * e, 2)
    assert lower >= lower2


def exhaustive_square_checks():
    total = 0
    for a in range(1, 4):
        for b in range(1, 5):
            possible = [(x, y) for x in range(a) for y in range(b)]
            for bits in range(1 << len(possible)):
                edges = {uv for i, uv in enumerate(possible) if bits & (1 << i)}
                check_square_identity(a, b, edges)
                total += 1
    return total


def check_failed_uncoloured_lift():
    t = 8
    vertices, aux = square_graph({(x, y) for x in range(2) for y in range(t)})
    idx = {uv: i for i, uv in enumerate(vertices)}
    cycle = [(0, 0), (1, 1), (0, 2), (1, 3)]
    for i in range(4):
        assert tuple(sorted((idx[cycle[i]], idx[cycle[(i + 1) % 4]]))) in aux
    assert len({x for x, y in cycle}) == 2
    assert len(aux) == t * (t - 1)
    # K_(2,t) has no injective Q_3: either bipartition class of Q_3 has size four.
    assert 2 < 2 ** (3 - 1)


def cube_edge(x, y):
    z = x ^ y
    return z > 0 and z & (z - 1) == 0


def check_canonical_disjoint_lifts():
    for d in range(2, 9):
        h = 1 << d
        top = 1 << (d - 1)
        vertical = {}
        for x in range(top):
            y = x ^ top
            vertical[x] = (x, y) if x.bit_count() % 2 == 0 else (y, x)
        assert len({v for uv in vertical.values() for v in uv}) == h
        for x in range(top):
            for i in range(d - 1):
                xp = x ^ (1 << i)
                a, b = vertical[x]
                ap, bp = vertical[xp]
                assert a != ap and b != bp and cube_edge(a, bp) and cube_edge(ap, b)
        # Alternating the orientation recovers a Q_d on these disjoint edges.
        for x, (a, b) in vertical.items():
            lo, hi = (a, b) if x.bit_count() % 2 == 0 else (b, a)
            assert (lo, hi) == (x, x ^ top)


def check_lee_parameters():
    for d in range(8, 201):
        h = 1 << d
        m = h // 2
        eps = Fraction(2 * d * d, h)
        assert 0 < eps <= Fraction(1, 2)
        product = 1
        for j in range(d):
            product *= m - j
        assert m ** d * eps.denominator <= (eps.numerator + eps.denominator) * product
        assert Fraction(3, 8) ** (d - 2) <= eps
        # Exact reduction rho^(d(d-2)) = ((1+eps)/C)^(d-2).
        for C in (4, 8, 16):
            assert ((1 + eps) / C) ** (d - 2) <= eps


def check_partite_cube():
    counts = []
    for d in (2, 4, 8, 16):
        h = 1 << d
        colours = [0] * h
        for x in range(1, h):
            low = x & -x
            i = low.bit_length() - 1
            colours[x] = colours[x ^ low] ^ i
        class_sizes = [0] * d
        for x in range(h):
            if x.bit_count() % 2 == 0:
                class_sizes[colours[x]] += 1
            else:
                cs = {colours[x ^ (1 << i)] for i in range(d)}
                assert cs == set(range(d))
        assert class_sizes == [h // (2 * d)] * d
        counts.append((d, h // (2 * d)))
    for d in range(2, 200):
        assert (((1 << (d - 1)) % d == 0) == (d & (d - 1) == 0))
    return counts


def check_exponents_and_constants():
    alpha = Fraction(1, 2)
    for d in range(2, 101):
        if d > 2:
            alpha = 2 * alpha / (2 + alpha)
        assert alpha == Fraction(2, d + 2)
        h = 1 << d
        ell = d * h // 2
        beta = Fraction(h - 2, ell - 1)
        diff = Fraction(2, d) - beta
        assert diff == Fraction(4 * (d - 1), d * (d * h - 2)) and diff > 0
        # Aut(Q_d)/(2 e(Q_d)) = (d-1)!.
        assert Fraction(h * factorial(d), 2 * ell) == factorial(d - 1)
    for d in range(8, 401):
        h = 2.0 ** d
        eps = 2 * d * d / h
        for C in (4.1, 5, 8, 16, 100):
            # Four times the hypothetical bound divided by N^2.
            direct_log = log(4) + log1p(eps) / d - Fraction(2, d + 2) * (log(C) + d * log(2))
            simplified_log = log1p(eps) / d + 2 * log(4 / C) / (d + 2)
            assert isclose(direct_log, simplified_log, rel_tol=1e-10, abs_tol=1e-14)
            if C >= 8:
                assert simplified_log < 0
        # Critical bookkeeping: exact formal L=2 recurrence tends to A_d=1.
    for L in (1, 1.5, 2, 3):
        logA = -log(2)
        for d in range(3, 201):
            prev = 2 / (d + 1)
            logA = (1 - 3 / (2 + prev)) * log(2) + (log(L) + logA) / (2 + prev)
            explicit = (((log(L, 2) - 1) * d + 2 - (16 + 8 * log(L, 2)) * 2 ** (-d)) / (d + 2)) * log(2)
            assert isclose(logA, explicit, abs_tol=1e-13)


def check_q3_algebra():
    rng = random.Random(318)
    for c, k, t in ((2.0, 2.0, 2.0), (2 ** (1 / 3), 16.0, 5.0)):
        for _ in range(3000):
            a = rng.randint(1, 1_000_000)
            b = rng.randint(1, 1_000_000)
            P, S = a * b, a + b
            T = a * b ** 0.5 + b * a ** 0.5
            X = c ** (3 / 5) * P ** (4 / 5)
            e = X + t * T
            f = (e - a) * (e - b) - c * e ** (1 / 3) * P ** (4 / 3) - k * S * P
            assert f > 0
            assert T >= S and T * T >= S * P
            assert t * (t - 1) >= k
    # Inductive treatment of leaf removal: the T contribution decreases by at least one.
    for a in range(1, 101):
        for b in range(1, 101):
            old = a * b ** 0.5 + b * a ** 0.5
            new = (a - 1) * b ** 0.5 + b * (a - 1) ** 0.5
            assert old - new >= 1 - 1e-10


def check_lower_constructions():
    for C in (Fraction(5, 4), Fraction(3, 2), Fraction(7, 4), Fraction(19, 10)):
        asym = (1 + (C - 1) ** 2) / (2 * C * C)
        assert asym > Fraction(1, 4)
        d = 16
        h = 1 << d
        N = C.numerator * h // C.denominator
        a, b = h - 1, N - h + 1
        assert a < h and b < h
        e = comb(a, 2) + comb(b, 2)
        assert 4 * e - N * N == (2 * h - 2 - N) ** 2 - 2 * N
        assert 4 * e > N * N
    for d in range(2, 31):
        h = 1 << d
        ell = d * h // 2
        for C in (1, 2, 8):
            N = C * h
            logp = (lgamma(d) - (h - 2) * log(N)) / (ell - 1)
            assert logp <= 0
            # Chosen p makes expected cube bound exactly p N^2 /(2 ell).
            left = h * log(N) + ell * logp - log(h) - lgamma(d + 1)
            right = logp + 2 * log(N) - log(2 * ell)
            # Cancellation grows with dimension, so use a relative scale tolerance.
            assert abs(left - right) <= 2e-7 * (1 + abs(h * log(N)))


def main():
    spec = Path(__file__).with_name('Spec.lean')
    before = hashlib.sha256(spec.read_bytes()).hexdigest() if spec.exists() else None
    n = exhaustive_square_checks()
    print(f'PASS: exact square identity and lower bounds on {n} bipartite graphs')
    check_failed_uncoloured_lift()
    print('PASS: K_(2,8) counterexample to uncoloured square-lift induction')
    check_canonical_disjoint_lifts()
    print('PASS: canonical disjoint cube lifts for 2<=d<=8')
    check_lee_parameters()
    print('PASS: exact Lee parameter inequalities for 8<=d<=200')
    print('PASS: partite Hamming-label classes', check_partite_cube())
    check_exponents_and_constants()
    print('PASS: random-alteration exponent, critical coefficient and formal square-recursion algebra')
    check_q3_algebra()
    print('PASS: Q3 lower-order-constant absorption and leaf-removal inequalities')
    check_lower_constructions()
    print('PASS: small-host clique obstructions and random-alteration normalization')
    if before is not None:
        assert hashlib.sha256(spec.read_bytes()).hexdigest() == before
        print('PASS: Spec.lean unchanged; SHA256=' + before)
    print('No check above asserts the unproved near-2/d extremal exponent or linear Ramsey bound.')


if __name__ == '__main__':
    main()
