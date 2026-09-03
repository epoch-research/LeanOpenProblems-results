#!/usr/bin/env python3
"""Finite audits for CubeIndependentAttackB.md; not a test of its open (26)."""
from collections import Counter
from fractions import Fraction
from itertools import permutations, product
from math import comb, exp, log, log2
from pathlib import Path
import hashlib
import random

import numpy as np

ROOT = Path(__file__).resolve().parent
RNG = random.Random(20260901)
EXPECTED_SPEC = "9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b"


def cube_edges(d):
    return [(v, v ^ (1 << i)) for v in range(1 << d)
            for i in range(d) if not (v & (1 << i))]


def matrix_from_mask(t, mask):
    return np.array([[(mask >> (i * t + j)) & 1 for j in range(t)]
                     for i in range(t)], dtype=np.int64)


def edge_set(t, mask):
    return {(i, j) for i in range(t) for j in range(t)
            if (mask >> (i * t + j)) & 1}


def square_graph(t, edges):
    labels = sorted(edges)
    adj = [0] * len(labels)
    for i, (x, y) in enumerate(labels):
        for j, (z, w) in enumerate(labels):
            if x != z and y != w and (x, w) in edges and (z, y) in edges:
                adj[i] |= 1 << j
    return labels, adj


def check_cross_law_and_planting():
    n_laws = 0
    for r in range(1, 5):
        q = comb(r, 2)
        counts = Counter()
        for bits in range(1 << (2 * q)):
            successes = sum(((bits >> (2 * j)) & 3) == 3 for j in range(q))
            counts[successes] += 1
        for j in range(q + 1):
            assert counts[j] == comb(q, j) * 3 ** (q - j)
        n_laws += 1

    r = 3
    cross = [(a, r + b) for i in range(r) for j in range(i + 1, r)
             for a, b in ((i, j), (j, i))]
    # The two cross-edges associated with each pair of matching labels are consecutive.
    assert len(cross) == 2 * comb(r, 2) and len(set(cross)) == len(cross)

    def count(bits):
        return sum(((bits >> (2 * j)) & 3) == 3 for j in range(comb(r, 2)))

    tested = 0
    for old in range(1 << len(cross)):
        for plant in range(1 << len(cross)):
            new_bits = plant & ~old
            deg = [0] * (2 * r)
            for j, (a, b) in enumerate(cross):
                if (new_bits >> j) & 1:
                    deg[a] += 1
                    deg[b] += 1
            created = count(old | plant) - count(old)
            assert created <= new_bits.bit_count() <= r * max(deg)
            tested += 1
    print(f"PASS cross-edge Binomial(q,1/4) law: {n_laws} exhaustive sizes")
    print(f"PASS planted-edge perturbation: {tested} exhaustive pairs of patterns")


def check_cube_induced_edges():
    total = 0
    for d in range(5):
        h = 1 << d
        neighbours = [sum(1 << (v ^ (1 << i)) for i in range(d))
                      for v in range(h)]
        counts = [0] * (1 << h)
        for mask in range(1 << h):
            if mask:
                low = mask & -mask
                v = low.bit_length() - 1
                rest = mask ^ low
                counts[mask] = counts[rest] + (neighbours[v] & rest).bit_count()
            s = mask.bit_count()
            # Equivalent to 2 e <= s log_2 s, without floating-point arithmetic.
            assert (1 << (2 * counts[mask])) <= (s ** s if s else 1)
            total += 1
    print(f"PASS cube induced-edge inequality: all {total} subsets for d=0,...,4")


def bipartite_maps(d, t):
    h = 1 << d
    evens = [v for v in range(h) if v.bit_count() % 2 == 0]
    odds = [v for v in range(h) if v.bit_count() % 2 == 1]
    oriented_edges = [(a, b) if a in evens else (b, a) for a, b in cube_edges(d)]
    for values in product(range(t), repeat=h):
        images = dict(zip(evens + odds, values))
        yield [(images[a], images[b]) for a, b in oriented_edges]


def check_holder_overlap():
    tested = 0
    for d, t in ((1, 2), (2, 2), (3, 2), (1, 3), (2, 3)):
        h = 1 << d
        m = h // 2
        maps = list(bipartite_maps(d, t))
        for mask in range(1 << (t * t)):
            edges = edge_set(t, mask)
            lhs = sum(1 << sum(e in edges for e in image) for image in maps)
            rhs = (t * t + (h - 1) * len(edges)) ** m
            assert lhs <= rhs, (d, t, mask, lhs, rhs)
            tested += 1
    print(f"PASS exact matching-factorization/Hölder overlap inequality: {tested} cases")


def endpoint_count(k, t, edges):
    m = 1 << k
    if t < m:
        return 0
    total = 0
    ced = cube_edges(k)
    perms = list(permutations(range(t), m))
    for rows in perms:
        for cols in perms:
            if not all((rows[z], cols[z]) in edges for z in range(m)):
                continue
            if all((rows[z], cols[w]) in edges and (rows[w], cols[z]) in edges
                   for z, w in ced):
                total += 1
    return total


def direct_cube_count(d, t, edges):
    h = 1 << d
    m = h // 2
    if t < m:
        return 0
    even = [v for v in range(h) if v.bit_count() % 2 == 0]
    odd = [v for v in range(h) if v.bit_count() % 2 == 1]
    es = [(a, b) if a in even else (b, a) for a, b in cube_edges(d)]
    total = 0
    perms = list(permutations(range(t), m))
    for rows in perms:
        for cols in perms:
            image = dict(zip(even + odd, rows + cols))
            if all((image[a], image[b]) in edges for a, b in es):
                total += 1
    return total


def auxiliary_count_small(k, t, edges):
    _, adj = square_graph(t, edges)
    if k == 1:
        return sum(x.bit_count() for x in adj)
    assert k == 2
    ans = 0
    for i in range(len(adj)):
        for j in range(len(adj)):
            if i != j:
                c = (adj[i] & adj[j]).bit_count()
                ans += c * (c - 1)
    return ans


def check_lift_counts_and_planted_expectation():
    tested = 0
    for t in range(1, 4):
        for mask in range(1 << (t * t)):
            edges = edge_set(t, mask)
            dk = endpoint_count(1, t, edges)
            assert dk == direct_cube_count(2, t, edges)
            assert dk == auxiliary_count_small(1, t, edges)
            tested += 1
    t = 4
    # Include the complete host, empty host, and a concrete planted Q_3.
    planted = set()
    rows = cols = tuple(range(4))
    for z in range(4):
        planted.add((rows[z], cols[z]))
    for z, w in cube_edges(2):
        planted.add((rows[z], cols[w]))
        planted.add((rows[w], cols[z]))
    hosts = [set(), edge_set(t, (1 << 16) - 1), planted]
    hosts += [edge_set(t, RNG.randrange(1 << 16)) for _ in range(128)]
    for edges in hosts:
        dk = endpoint_count(2, t, edges)
        assert dk == direct_cube_count(3, t, edges)
        assert dk <= auxiliary_count_small(2, t, edges)
        tested += 1
    assert endpoint_count(2, 4, planted) > 0

    expected_cases = 0
    for k, t, u in ((1, 2, 1), (1, 3, 1), (2, 4, 2), (2, 5, 2)):
        m, d = 1 << k, k + 1
        T = {(z, z) for z in range(m)}
        for z, w in cube_edges(k):
            T.update(((z, w), (w, z)))
        assert len(T) == d * m
        P = {(i, j) for i in range(u) for j in range(u)}
        forced = T | P
        expected = Fraction(0)
        perms = list(permutations(range(t), m))
        for rows in perms:
            for cols in perms:
                need = {(rows[z], cols[z]) for z in range(m)}
                for z, w in cube_edges(k):
                    need.update(((rows[z], cols[w]), (rows[w], cols[z])))
                assert len(need) == d * m
                expected += Fraction(1, 1 << len(need - forced))
        U = Fraction((2 * u) ** u * (t * t + (2 * m - 1) * d * m) ** m,
                     1 << (d * m))
        assert expected <= U
        expected_cases += 1
    print(f"PASS endpoint-lift counting bijection: {tested} bipartite hosts")
    print(f"PASS planted injective-cube expectation bound: {expected_cases} exact averages")


def check_kernel_and_fourth_moment():
    tested = 0
    for t in range(1, 4):
        full_labels = [(i, j) for i in range(t) for j in range(t)]
        trace_sum = 0
        for mask in range(1 << (t * t)):
            M = matrix_from_mask(t, mask)
            K = np.array([[M[x, w] * M[z, y] for z, w in full_labels]
                          for x, y in full_labels], dtype=np.int64)
            X = np.arange(t * t, dtype=np.int64).reshape(t, t)
            assert np.array_equal((K @ X.ravel()).reshape(t, t), M @ X.T @ M)
            labels, adj = square_graph(t, edge_set(t, mask))
            inds = [x * t + y for x, y in labels]
            n = len(labels)
            A = np.array([[(adj[i] >> j) & 1 for j in range(n)]
                          for i in range(n)], dtype=np.int64).reshape(n, n)
            restricted = K[np.ix_(inds, inds)]
            conflict = np.array([[int(x == z or y == w) for z, w in labels]
                                 for x, y in labels], dtype=np.int64).reshape(n, n)
            assert np.array_equal(restricted - A, conflict)
            if n:
                assert max(conflict.sum(axis=1)) <= 2 * t - 1
                wnorm = np.linalg.norm(M - 0.5, 2)
                lhs = np.linalg.norm(A - 0.25, 2)
                rhs = t * wnorm + wnorm * wnorm + 2 * t - 1
                assert lhs <= rhs + 1e-10
            signs = 2 * M - 1
            Z = signs @ signs.T
            trace_sum += int(np.trace(Z @ Z))
            tested += 1
        assert trace_sum == (1 << (t * t)) * (2 * t**3 - t**2)
    print(f"PASS full-square kernel, conflict correction, and norm bound: {tested} matrices")
    print("PASS random-matrix fourth moment: exact averages for t=1,2,3")


def check_finite_constants():
    ks = list(range(256, 4097)) + [8192, 16384, 65536]
    max_error = 0.0
    max_delta = 0.0
    for k in ks:
        p = lambda a: 2.0 ** (-a * k)
        tail = ((0.75 + 1.0 / k) * p(0.25)
                + (4 * p(0.75) + 4.0 / k * p(0.5)) / log(2)
                + 2.0 / k * p(1.0))
        assert tail < 1 / 64
        # Maximize the allowed C contribution, 2 log_2(C+1)/k <= 1/8.
        error = 1.0 / k + 1 / 8 + log2(2 * k + 3) / k + tail
        delta = p(0.125) + 2 * (p(0.25) + (k + 1) * p(1.0)) / (1 - p(1.0))
        assert error < 1 / 4 and delta < 1 / 12
        assert 2 * p(0.25) <= p(0.125)  # u+d <= t^(7/8), using d<=m^(3/4)
        assert 4 * p(0.125) + 2 * p(0.875) < 1  # spectral 3 t^(15/8)
        max_error = max(max_error, error)
        max_delta = max(max_delta, delta)
    # Logarithms of the five probability terms at the worst endpoint k=256.
    k = 256
    lm = k * log(2)
    log_terms = [-(2.0 ** (7 * k / 8)) / 64,
                 -(2.0 ** (7 * k / 8)) / 32,
                 log(8) + lm - 2 * 2.0 ** (k / 2),
                 17 / 16 * lm - 2.0 ** (7 * k / 4) / 4,
                 -log(8) - lm / 2]
    assert all(x < -64 * log(2) for x in log_terms)
    assert 2.0 ** (3 * k / 4) * (1 - 2.0 ** (-k)) >= 4 * (log(2) + 17 / 16 * lm)

    # A finite comparison for the complete-biclique auxiliary C4 counts.
    for u in (12, 16, 24, 32):
        k, m = 2, 4
        c1, c2 = (u - 1) * (u - 2), (u - 2) ** 2
        exact_I = (2 * u * u * (u - 1) * c1 * (c1 - 1)
                   + u * u * (u - 1)**2 * c2 * (c2 - 1))
        log_L = 2 * m * log(u) - 2 * k * m / u - m * (m - 1) / (u * u)
        assert log(exact_I) >= log_L
    print(f"PASS finite entropy-gap constants: {len(ks)} dimensions, worst correction={max_error:.9f}<1/4")
    print(f"PASS all-matching density constants: worst delta={max_delta:.12g}<1/12")
    print("PASS all five probability tails at k=256 are individually <2^-64")
    print("PASS auxiliary greedy lower bound against exact complete-biclique counts")


def check_conditional_sufficiency():
    cases = 0
    for K in (Fraction(0), Fraction(1, 2), Fraction(1), Fraction(10)):
        for eps in (Fraction(1, 4), Fraction(1), Fraction(19, 10)):
            c0 = max(Fraction(6), 128 * (K + 1) / eps)
            C = (c0.numerator + c0.denominator - 1) // c0.denominator
            for d in range(1, 129):
                h = 1 << d
                m = h // 2
                N = C * h
                emin = Fraction(N * (N - 1), 8)
                assert emin >= 4 * h * h
                lower = 8 * emin * emin / N**4 - Fraction(N - 1, 2) / emin
                assert lower >= Fraction(1, 8) - Fraction(17, 4 * N)
                errors = 8 * K * m / (N - 1) + Fraction(17, 4 * N)
                assert errors <= (8 * K + Fraction(17, 8)) / C < eps / 16
                cases += 1
    print(f"PASS conditional sufficiency arithmetic for the explicitly UNPROVED estimate: {cases} cases")


def main():
    check_cross_law_and_planting()
    check_cube_induced_edges()
    check_holder_overlap()
    check_lift_counts_and_planted_expectation()
    check_kernel_and_fourth_moment()
    check_finite_constants()
    check_conditional_sufficiency()
    digest = hashlib.sha256((ROOT / "Spec.lean").read_bytes()).hexdigest()
    assert digest == EXPECTED_SPEC
    print(f"PASS Spec.lean unchanged: {digest}")
    print("All finite audits passed. The densegraph cube theorem and estimate (26) remain unproved.")


if __name__ == "__main__":
    main()
