#!/usr/bin/env python3
"""Exact finite checks for extremal_distance_cover_geometry.md.

The asymptotic proof is in the Markdown file. These checks use integer
coordinates, not floating-point distance equality. No Lean file is edited.
"""
from collections import defaultdict
from itertools import product, combinations
from math import isqrt, log, sqrt
from random import Random
import hashlib
from pathlib import Path


def norm2(p):
    return p[0] * p[0] + p[1] * p[1]


def dist2(p, q):
    return (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2


def cmul(p, q):
    return (p[0] * q[0] - p[1] * q[1],
            p[0] * q[1] + p[1] * q[0])


def neg(p):
    return (-p[0], -p[1])


def cross(o, a, b):
    return ((a[0] - o[0]) * (b[1] - o[1])
            - (a[1] - o[1]) * (b[0] - o[0]))


def hull_vertices(points):
    pts = sorted(set(points))
    if len(pts) <= 1:
        return pts
    lower, upper = [], []
    for p in pts:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    for p in reversed(pts):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    return lower[:-1] + upper[:-1]


def onion_depths(points):
    remaining = set(points)
    ans = {}
    depth = 1
    while remaining:
        h = set(hull_vertices(remaining))
        assert h
        for p in h:
            ans[p] = depth
        remaining -= h
        depth += 1
    return ans


def canonical_b(b):
    for x in b:
        if x:
            return b if x > 0 else tuple(-y for y in b)
    return b


def cap(k):
    signs = list(product((-1, 1), repeat=k))
    points = []
    for eps in signs:
        p = (1, 0)
        for j, e in enumerate(eps, 1):
            p = cmul(p, (10 ** j, e))
        points.append(p)
    return signs, points


def basic_parameters(k):
    N, z = 1, (1, 0)
    for j in range(1, k + 1):
        a = 10 ** j
        N *= a * a + 1
        z = cmul(z, (a, 1))
    A, B = z
    assert norm2(z) == N
    m = isqrt(N) // 20  # Exactly floor(sqrt(N)/20).
    n = (2 * m + 1) ** 2 + 2 ** (k + 1)
    return N, A, B, m, n


def verify_cap_spectrum(k):
    signs, pos = cap(k)
    N, A, B, m, n = basic_parameters(k)
    M = len(pos)
    outer = pos + [neg(p) for p in pos]
    assert M == 2 ** k
    assert len(set(outer)) == 2 ** (k + 1)
    assert all(norm2(p) == N and p[0] > 0 for p in pos)
    assert 0 < B < A and 101 * B * B >= N
    assert m >= 1 and m < B and m < A
    corners = list(product((-m, m), repeat=2))
    assert set(hull_vertices(outer + corners)) == set(outer)

    edges = defaultdict(list)
    labels = {}
    for i, p in enumerate(pos):
        for j, q in enumerate(pos):
            # The actual edge is p -- (-q).
            s = dist2(p, neg(q))
            assert 4 * s > 9 * N
            b = canonical_b(tuple((x - y) // 2
                                  for x, y in zip(signs[i], signs[j])))
            if s in labels:
                assert labels[s] == b
            else:
                labels[s] = b
            edges[s].append((i, M + j))

    assert len(edges) == (3 ** k + 1) // 2
    assert max(edges) == 4 * N
    for s, es in edges.items():
        b = labels[s]
        h = sum(x != 0 for x in b)
        expected = 2 ** k if h == 0 else 2 ** (k - h + 1)
        assert len(es) == expected
        endpoints = [v for e in es for v in e]
        assert len(set(endpoints)) == 2 * expected  # Exact matching.

    ordered = sorted(edges, reverse=True)
    for r in range(k + 1):
        T = (3 ** r + 1) // 2
        expected_labels = {b for b in labels.values()
                           if all(x == 0 for x in b[:k-r])}
        assert {labels[s] for s in ordered[:T]} == expected_labels
        assert len(expected_labels) == T
        assert min(len(edges[s]) for s in ordered[:T]) >= 2 ** (k-r)

    for p, q in combinations(pos, 2):
        assert 4 * dist2(p, q) < 9 * N
    # The core lies in the disk of radius R/10, and no non-cap-opposite
    # distance can enter the upper band. Check the extreme pairs exactly.
    assert 200 * m * m <= N
    assert all(4 * dist2(p, q) < 9 * N
               for p in outer for q in corners)
    assert all(4 * dist2(p, q) < 9 * N
               for p, q in combinations(corners, 2))

    rare = 4 * A * A
    zplus, zminus = (A, B), (A, -B)
    wanted_rare = {frozenset((zplus, neg(zminus))),
                   frozenset((zminus, neg(zplus)))}
    found_rare = {frozenset((outer[i], outer[j]))
                  for i, j in edges[rare]}
    assert found_rare == wanted_rare and len(edges[rare]) == 2
    assert min(ordered) == rare

    cross_max = N + 2 * m * m + 2 * m * (A + B)
    corner_cross = [(dist2(p, q), p, q) for p in outer for q in corners]
    assert max(s for s, _, _ in corner_cross) == cross_max
    found_max = {frozenset((p, q)) for s, p, q in corner_cross
                 if s == cross_max}
    wanted_max = {
        frozenset(((A, B), (-m, -m))),
        frozenset(((A, -B), (-m, m))),
        frozenset(((-A, -B), (m, m))),
        frozenset(((-A, B), (m, -m))),
    }
    assert found_max == wanted_max
    assert len({v for e in wanted_max for v in e}) == 8
    assert N < cross_max and 4 * cross_max < 9 * N

    # Filled-disk witnesses: all are actual interior integer endpoints.
    u, v = B * B // (8 * A), B // 2
    worst_norm = (A + u) ** 2 + v * v
    assert worst_norm < N
    assert u < A
    matching_size = (2 * u + 1) * (2 * v + 1)
    assert 16 * A * matching_size >= B ** 3

    if k == 2:
        grid = list(product(range(-m, m+1), repeat=2))
        all_cross = [(dist2(p, q), p, q) for p in outer for q in grid]
        assert max(s for s, _, _ in all_cross) == cross_max
        assert {frozenset((p, q)) for s, p, q in all_cross
                if s == cross_max} == wanted_max
        assert all(s != rare for s, _, _ in all_cross)
        palette = {x*x+y*y for x in range(2*m+1)
                   for y in range(2*m+1) if x or y}
        palette.update(s for s, _, _ in all_cross)
        palette.update(dist2(p, q) for p, q in combinations(outer, 2))
        assert sorted(palette, reverse=True)[:len(ordered)] == ordered
        print(f"  Full P_2 palette: n={n}, D={len(palette)}, "
              f"K={n/len(palette):.6f}; this small k is not the asymptotic regime.")
        endpoints = set()
        for t in range(-u, u+1):
            for y in range(-v, v+1):
                p, q = (-A+t, y), (A+t, y)
                assert norm2(p) < N and norm2(q) < N
                assert dist2(p, q) == rare
                assert p not in endpoints and q not in endpoints
                endpoints.add(p)
                endpoints.add(q)
        assert len(endpoints) == 2 * matching_size
        Rfloor = isqrt(N)
        n_disk = sum(2 * isqrt(N-x*x) + 1
                     for x in range(-Rfloor, Rfloor+1))
        assert n_disk <= 9 * N
        print(f"  Filled disk Q_2: n={n_disk}, certified same-color "
              f"matching={matching_size}; every endpoint checked.")

    print(f"k={k}: outer={len(outer)}, longest colors={len(edges)}, "
          f"diameter cover={M}, rare cover=2, cross-maximum cover=4: PASS")


def verify_onion_and_cross_max():
    rng = Random(20260902)
    cases = [list(product(range(5), repeat=2)),
             [(i, 0) for i in range(13)],
             [(0, 0), (1, 0)],
             [(0, 0), (2, 0), (1, 1), (1, -1), (1, 0)]]
    for _ in range(200):
        P = set()
        while len(P) < rng.randint(6, 22):
            P.add((rng.randrange(-12, 13), rng.randrange(-12, 13)))
        cases.append(sorted(P))
    for P in cases:
        depth = onion_depths(P)
        lengths = sorted({dist2(p, q) for p, q in combinations(P, 2)},
                         reverse=True)
        rank = {s: j for j, s in enumerate(lengths, 1)}
        for p, q in combinations(P, 2):
            j = rank[dist2(p, q)]
            assert depth[p] + depth[q] <= j + 1
            assert min(depth[p], depth[q]) <= (j+1)//2
        cut = len(P) // 2
        AA, BB = P[:cut], P[cut:]
        if AA and BB:
            cross_d = max(dist2(a, b) for a in AA for b in BB)
            hA, hB = set(hull_vertices(AA)), set(hull_vertices(BB))
            assert all(a in hA and b in hB
                       for a in AA for b in BB if dist2(a, b) == cross_d)
    print(f"Onion rank/depth and cross-maximum endpoint checks: "
          f"{len(cases)} actual point sets: PASS")


def large_parameter_checks():
    print("Large-k exact parameter checks (not enumeration, not a numerical "
          "test of Landau--Ramanujan):")
    for k in (16, 32, 64, 128):
        N, A, B, m, n = basic_parameters(k)
        r = k // 4
        T = (3 ** r + 1) // 2
        assert A*A+B*B == N and 0 < B < A
        assert 101*B*B >= N and m < B
        u, v = B*B//(8*A), B//2
        assert (A+u)**2+v*v < N
        assert 16*A*(2*u+1)*(2*v+1) >= B**3
        assert abs(log(n) - k*(k+1)*log(10)) < 5
        print(f"  k={k:3d}: log n={log(n):.3f}; "
              f"log(min first-T cover / sqrt(log n)) >= "
              f"{(k-r)*log(2)-0.5*log(log(n)):.3f}; "
              f"log(prefix-cover/(T sqrt(log n))) = "
              f"{k*log(2)-log(T)-0.5*log(log(n)):.3f}")


def main():
    print("All equality checks below use exact integer squared distances.")
    for k in range(2, 9):
        verify_cap_spectrum(k)
    verify_onion_and_cross_max()
    large_parameter_checks()
    spec = Path(__file__).with_name('Spec.lean')
    print("Spec.lean SHA256:", hashlib.sha256(spec.read_bytes()).hexdigest())
    print("ALL CHECKS PASSED. Asymptotic and universal-quantifier arguments "
          "are proved in the accompanying Markdown, not inferred from these tests.")


if __name__ == '__main__':
    main()
