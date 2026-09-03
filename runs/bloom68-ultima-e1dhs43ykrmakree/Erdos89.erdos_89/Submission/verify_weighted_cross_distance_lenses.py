#!/usr/bin/env python3
"""Exact finite checks for weighted_cross_distance_lenses.md.

All distance equalities, fiber multiplicities, circumcenters, lens tests,
weights, and support counts are integer/rational exact. Decimal output is
only for readability. Large-grid edge tests enumerate complete circle
fibers, not all grid points. No numerical optimization over all disks or
numerical verification of an asymptotic theorem is claimed.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import comb, isqrt, lcm
import random

import numpy as np

from verify_geometric_cross_distance_certificates import (
    circumcenter, compositions, lens_over_edge, sqdist,
)
from verify_disk_capacity_localization import exact_support


def binom3(k: int) -> int:
    return comb(k, 3) if k >= 3 else 0


def f2(k: int) -> F:
    return F(binom3(k), k*k) if k else F(0)


def canonical_edge(triple):
    pairs = list(combinations(triple, 2))
    lengths = [sqdist(*edge) for edge in pairs]
    largest = max(lengths)
    assert lengths.count(largest) == 1
    edge = tuple(sorted(pairs[lengths.index(largest)]))
    third = next(z for z in triple if z not in edge)
    return edge, third


def check_balanced_weights():
    tests = 0
    for m in range(15):
        for d in range(1, 6):
            values = [sum((f2(k) for k in ks), F(0))
                      for ks in compositions(m, d)]
            q, u = divmod(m, d)
            balanced = (d-u)*f2(q) + u*f2(q+1)
            assert min(values) == balanced
            if m > 2*d:
                assert balanced >= F((m-d)*(m-2*d), 6*m)
                assert F(m*m, d*d)*balanced >= F(m*(m-d)*(m-2*d), 6*d*d)
            tests += 1
    for k in range(1, 201):
        assert 6*f2(k) == k-3+F(2, k)
        if k >= 3:
            keep_probability = f2(k)/(k//3)
            assert F(1, 9) <= keep_probability <= F(1, 2)
    print(f'Balanced inverse-square minima and finite support lower bound: PASS ({tests} parameter pairs)')


def check_witness_couplings():
    cases = 0
    for k in range(3, 8):
        frequencies = Counter()
        total = 0
        for perm in permutations(range(k)):
            chosen = [tuple(sorted(perm[3*j:3*j+3])) for j in range(k//3)]
            assert len(set().union(*(set(t) for t in chosen))) == 3*len(chosen)
            frequencies.update(chosen)
            total += 1
        assert len(frequencies) == binom3(k)
        keep_probability = f2(k)/(k//3)
        for t, frequency in frequencies.items():
            assert F(frequency, total) == F(k//3, binom3(k))
            assert F(frequency, total)*keep_probability == F(1, k*k)
        # One uniformly selected triple is the color-normalized coupling.
        assert sum((F(1, binom3(k)) for _ in combinations(range(k), 3)), F(0)) == 1
        cases += 1
    print(f'Exact row-disjoint witness couplings: PASS ({cases} fiber sizes, all permutations through k=7)')


def check_geometry_instance(name, A, B, c, r, R):
    assert R > r >= 0 and A and B
    assert len(A) == len(set(A)) and len(B) == len(set(B))
    assert all(sqdist(a, c) <= r*r for a in A)
    assert all(sqdist(p, c) >= R*R for p in B)
    m, s = len(A), len(B)
    rows = {}
    histogram = Counter()
    rich_occurrences = Counter()
    for p in B:
        fibers = defaultdict(list)
        for a in A:
            fibers[sqdist(p, a)].append(a)
        rows[p] = dict(fibers)
        histogram.update(len(fiber) for fiber in fibers.values())
        rich_occurrences.update(d for d, fiber in fibers.items() if len(fiber) >= 3)
    d_cross = len(set().union(*(set(row) for row in rows.values())))
    D_rows = sum(histogram.values())
    H_rows = sum((F(count, k) for k, count in histogram.items()), F(0))
    U2 = sum((count*f2(k) for k, count in histogram.items()), F(0))
    U0 = sum(count for k, count in histogram.items() if k >= 3)
    assert 6*U2 == s*m-3*D_rows+2*H_rows
    assert U2 <= F(s*m, 6)
    if m > 2*d_cross:
        assert F(m*m, d_cross*d_cross)*U2 >= F(s*m*(m-d_cross)*(m-2*d_cross), 6*d_cross*d_cross)

    triangles = {}
    endpoint2 = defaultdict(F)
    endpoint0 = defaultdict(F)
    endpoint_global = defaultdict(F)
    for p, fibers in rows.items():
        for d, fiber in fibers.items():
            k = len(fiber)
            for triple in combinations(fiber, 3):
                key = tuple(sorted(triple))
                assert key not in triangles  # unique actual circumcenter
                triangles[key] = (p, d, k)
                assert circumcenter(*triple) == p
                edge, z = canonical_edge(triple)
                assert lens_over_edge(*edge, z, R-r)
                endpoint2[edge] += F(1, k*k)
                endpoint0[edge] += F(1, binom3(k))
                endpoint_global[edge] += F(1, rich_occurrences[d]*binom3(k))
    assert sum(endpoint2.values(), F(0)) == U2
    assert sum(endpoint0.values(), F(0)) == U0
    assert sum(endpoint_global.values(), F(0)) == len(rich_occurrences)

    # Independent triple enumeration, not just circle-fiber generation.
    Bset = set(B)
    direct = {tuple(sorted(t)) for t in combinations(A, 3) if circumcenter(*t) in Bset}
    assert direct == set(triangles)

    # Independent endpoint disintegration, using chord comparisons.
    direct2, direct0 = defaultdict(F), defaultdict(F)
    for a, b in combinations(A, 2):
        edge = tuple(sorted((a, b)))
        length2 = sqdist(a, b)
        for p, fibers in rows.items():
            d = sqdist(p, a)
            if d != sqdist(p, b):
                continue
            fiber = fibers[d]
            k = len(fiber)
            ell = sum(z not in edge and sqdist(a, z) < length2 and sqdist(b, z) < length2
                      for z in fiber)
            if ell:
                direct2[edge] += F(ell, k*k)
                direct0[edge] += F(ell, binom3(k))
    assert dict(direct2) == dict(endpoint2)
    assert dict(direct0) == dict(endpoint0)

    # The exact light-mass repair is checked row by row.
    for p, fibers in rows.items():
        rich_mass = sum(len(fiber) for fiber in fibers.values() if len(fiber) >= 3)
        if rich_mass:
            repaired = sum((F(m, rich_mass)*k
                            for k in map(len, fibers.values()) if k >= 3), F(0))
            assert repaired == m
    print(f'  {name}: m={m}, s={s}, cross D={d_cross}, actual triples={len(triangles)}, '
          f'U2={U2}, U0={U0}, rich global colors={len(rich_occurrences)}')


def check_geometry():
    print('Actual-circumcenter, endpoint, and global-color identities:')
    arc = [(65, 0), (63, 16), (63, -16), (56, 33), (56, -33)]
    check_geometry_instance('five-point Pythagorean arc', arc, [(0, 0)],
                            (65, 0), 35, 65)
    near = arc + [(F(65)+F(1, 10**40), 0)]
    check_geometry_instance('support change at separation 10^(-40)', near, [(0, 0)],
                            (65, 0), 35, 65)
    symmetric = [(x, y) for x in range(-3, 4) for y in (-3, -2, -1, 1, 2, 3)]
    check_geometry_instance('two exterior centers', symmetric, [(-5, 0), (5, 0)],
                            (0, 0), F(9, 2), 5)
    A = [(x, y) for x in range(-3, 4) for y in range(-3, 4) if x*x+y*y <= 9]
    B = [(x, y) for x in range(-8, 9) for y in range(-8, 9) if x*x+y*y >= 36]
    check_geometry_instance('complete disk in a unit grid', A, B, (0, 0), 3, 6)
    rng = random.Random(20270119)
    ambient = list(product(range(-4, 5), repeat=2))
    exterior = [(x, y) for x in range(-12, 13) for y in range(-12, 13)
                if x*x+y*y >= 100]
    for trial in range(5):
        check_geometry_instance(f'exact random configuration {trial+1}',
                                rng.sample(ambient, 16), rng.sample(exterior, 9),
                                (0, 0), 6, 10)
    print('  PASS: full fiber weights retained, with no distance tolerances')


def distance_support(points):
    return {sqdist(a, b) for a, b in combinations(points, 2)}


def check_forced_stars():
    print('Forced-chord rational/integer stars (M_disk = 2):')
    subset_checks = 0
    for N in (1, 2, 4, 8, 16, 32):
        a, b = (F(-1), F(0)), (F(1), F(0))
        A = [a, b] + [(F(0), -F(1, j)) for j in range(3, N+3)]
        B = [(F(0), F(j*j-1, 2*j)) for j in range(3, N+5)]
        P = A+B
        assert len(A) == len(B) == N+2
        assert all(sqdist(x, (0, 0)) <= 1 for x in A)
        assert all(sqdist(x, (0, 0)) >= F(16, 9) for x in B)
        # These facts prove the pinned |Q|-1 bound for every subset Q.
        axis = P[2:]
        assert len({abs(x[1]) for x in axis}) == len(axis)
        assert all(x[0] == 0 for x in axis)
        for endpoint in (a, b):
            assert len({sqdist(endpoint, x) for x in P if x != endpoint}) == len(P)-1
        if N <= 4:
            for size in range(2, len(P)+1):
                for Q in combinations(P, size):
                    assert len(distance_support(Q)) >= size-1
                    subset_checks += 1
        weighted2, weighted0 = F(0), F(0)
        rich_radii = Counter()
        for p in B:
            row = Counter(sqdist(p, x) for x in A)
            k = row[sqdist(p, a)]
            assert k in (2, 3)
            if k == 3:
                weighted2 += F(1, 9)
                weighted0 += 1
                rich_radii[sqdist(p, a)] += 1
            assert all(count == 1 for d, count in row.items() if d != sqdist(p, a))
        assert weighted2 == F(N, 9) and weighted0 == N
        assert len(rich_radii) == N and set(rich_radii.values()) == {1}
        scale = 2*lcm(*range(3, N+5))
        scaled = [(x*scale, y*scale) for x, y in P]
        assert all(x.denominator == y.denominator == 1 for x, y in scaled)
        closest = min(combinations(P, 2), key=lambda pair: sqdist(*pair))
        u, v = closest
        center = ((u[0]+v[0])/2, (u[1]+v[1])/2)
        radius2 = sqdist(u, v)/4
        assert sum(sqdist(x, center) <= radius2 for x in P) == 2
        print(f'  N={N}: n={len(P)}, |A|={len(A)}, edge U0={weighted0}, edge U2={weighted2}; integer scaling checked')
    print(f'  PASS: {subset_checks} subsets also checked exhaustively for N<=4')


def disk_count(radius: int, strict: bool = False) -> int:
    bound = radius*radius-(1 if strict else 0)
    if bound < 0:
        return 0
    return sum(2*isqrt(bound-x*x)+1 for x in range(-radius, radius+1) if x*x <= bound)


def circle_cap(L: int, H: int):
    points = []
    for y in range(-L, 1):
        x2 = L*L+2*H*y-y*y
        if x2 < 0:
            continue
        x = isqrt(x2)
        if x*x != x2:
            continue
        points.append((x, y))
        if x:
            points.append((-x, y))
    return points


def divisor_and_representation_count(value: int):
    n = value
    divisor_count, representation_count = 1, 4
    p = 2
    while p*p <= n:
        exponent = 0
        while n % p == 0:
            n //= p
            exponent += 1
        if exponent:
            divisor_count *= exponent+1
            if p % 4 == 1:
                representation_count *= exponent+1
            elif p % 4 == 3 and exponent % 2:
                representation_count = 0
        p = 3 if p == 2 else p+2
    if n > 1:
        divisor_count *= 2
        if n % 4 == 1:
            representation_count *= 2
        elif n % 4 == 3:
            representation_count = 0
    return divisor_count, representation_count


def check_grid_edge_congestion(quick: bool):
    print('Full unit-grid fixed-chord congestion (complete actual circle fibers):')
    sizes = (25, 50, 100, 200, 400) if quick else (25, 50, 100, 200, 400, 800, 1600, 3200, 6400)
    centers_checked = 0
    for L in sizes:
        n = (8*L+1)**2
        m = disk_count(L)
        s = n-disk_count(2*L, strict=True)
        assert 2 <= m <= n//2 and s >= n//2
        edge = ((-L, 0), (L, 0))
        first = 2*L + ((7*L-2*L) % 25)
        centers = range(first, 3*L+1, 25)
        assert len(centers) >= L//25
        load0, load2 = F(0), F(0)
        kmax, rmax = 0, 0
        vx_min, vx_max, vy_max = -(L//4), -((L+7)//8), L//8
        translation_count = (vx_max-vx_min+1)*(vy_max+1)
        assert translation_count >= F(L*L, 128)
        translation_corners = list(product((vx_min, vx_max), (0, vy_max)))
        for H in centers:
            p = (0, H)
            z = ((24*L-7*H)//25, (H-7*L)//25)
            assert (24*L-7*H) % 25 == (H-7*L) % 25 == 0
            assert z[0] > 0 and z[1] < 0
            assert sqdist(z, (0, 0)) < L*L
            assert circumcenter(*edge, z) == p
            assert lens_over_edge(*edge, z, L)
            fiber = circle_cap(L, H)
            k = len(fiber)
            assert k >= 4
            assert set(edge+(z, (-z[0], z[1]))) <= set(fiber)
            assert all(sqdist(p, point) == L*L+H*H for point in fiber)
            assert all(sqdist(point, (0, 0)) <= L*L for point in fiber)
            pattern = (edge[1], z, (-z[0], z[1]))
            # Corner containment, plus convexity, certifies every integer
            # translation in the rectangle as a rich center of this radius.
            for vx, vy in translation_corners:
                shifted = tuple((point[0]+vx, point[1]+vy) for point in pattern)
                center = (vx, H+vy)
                assert all(sqdist(point, (0, 0)) <= L*L for point in shifted)
                assert center[1] >= 2*L and max(map(abs, center)) <= 4*L
                assert circumcenter(*shifted) == center
                assert all(sqdist(point, center) == L*L+H*H for point in shifted)
            ell = sum(point not in edge and sqdist(edge[0], point) < 4*L*L
                      and sqdist(edge[1], point) < 4*L*L for point in fiber)
            assert ell == k-2
            tau, r2 = divisor_and_representation_count(L*L+H*H)
            assert k <= r2 <= 4*tau
            if L <= 50:
                direct_r2 = 0
                for x in range(-isqrt(L*L+H*H), isqrt(L*L+H*H)+1):
                    y2 = L*L+H*H-x*x
                    y = isqrt(y2)
                    if y*y == y2:
                        direct_r2 += 1 if y == 0 else 2
                assert direct_r2 == r2
            load0 += F(ell, binom3(k))
            load2 += F(ell, k*k)
            assert F(ell, binom3(k)) == F(6, k*(k-1))
            kmax, rmax = max(kmax, k), max(rmax, r2)
            centers_checked += 1
        assert load0 >= F(6*len(centers), kmax*kmax)
        assert load2 >= F(len(centers), 2*kmax)
        print(f'  L={L:4d}: n={n}, selected centers={len(centers):3d}, '
              f'max k={kmax:3d}, max full r2={rmax:3d}, '
              f'edge U0>={float(load0):.6f}, edge U2>={float(load2):.6f}; '
              f't_delta>={translation_count}, selected global-color load<={float(load0/translation_count):.8f}')
    print(f'  PASS: {centers_checked} complete fibers and {4*centers_checked} translation-rectangle corners checked; '
          f'asymptotic divergence uses the proved divisor bound')


def check_full_grid_normalization(quick: bool):
    print('Full unit-grid aggregate weights and exact squared-ratio correction:')
    sizes = (2, 4, 8, 12) if quick else (2, 4, 8, 12, 16, 24, 32)
    total_rows = 0
    for L in sizes:
        axis = np.arange(-L, L+1, dtype=np.int64)
        xx, yy = np.meshgrid(axis, axis)
        mask = xx*xx+yy*yy <= L*L
        ax, ay = xx[mask], yy[mask]
        m, n = len(ax), (8*L+1)**2
        palette = {x*x+y*y for x in range(8*L+1) for y in range(8*L+1)} - {0}
        d = len(palette)
        local_palette = exact_support(mask)
        assert local_palette <= palette
        if L <= 4:
            assert local_palette == distance_support(list(zip(map(int, ax), map(int, ay))))
        histogram = Counter()
        s = 0
        for px in range(4*L+1):
            for py in range(px+1):
                if px*px+py*py < 4*L*L:
                    continue
                orbit = 4 if py == 0 or px == py else 8
                _, counts = np.unique((ax-px)**2+(ay-py)**2, return_counts=True)
                count_hist = np.bincount(counts)
                for k in np.nonzero(count_hist)[0]:
                    histogram[int(k)] += orbit*int(count_hist[k])
                s += orbit
        assert s == n-disk_count(2*L, strict=True)
        assert sum(k*count for k, count in histogram.items()) == s*m
        d_rows = sum(histogram.values())
        h_rows = sum((F(count, k) for k, count in histogram.items()), F(0))
        U2 = sum((count*f2(k) for k, count in histogram.items()), F(0))
        assert 6*U2 == s*m-3*d_rows+2*h_rows
        assert U2 <= F(s*m, 6)
        weighted = F(m*m, d*d)*U2
        if m > 2*d:
            assert weighted >= F(s*m*(m-d)*(m-2*d), 6*d*d)
        M_A2 = F(m*m, len(local_palette)**2)
        assert weighted <= F(s*m, 6)*M_A2
        Phi = F(n*n, d*d)
        W = F(6*n*n, s*m*d*d)*U2
        Gamma = F(n*n, s*m*d*d)*(3*d_rows-2*h_rows)
        assert W+Gamma == Phi
        assert Phi*F(d_rows, s*m) <= Gamma <= 3*Phi*F(d_rows, s*m)
        assert Gamma <= F(3*n*n, m*d)
        total_rows += s
        print(f'  L={L:2d}: n={n:6d}, m={m:4d}, s={s:6d}, D={d:5d}, '
              f'Phi={float(Phi):.6f}, W={float(W):.6f}, Gamma={float(Gamma):.6f}, '
              f'U2/(sm)={float(U2/F(s*m)):.8f}, K(A)^2={float(M_A2):.6f}')
    print(f'  PASS: exact aggregate weights for {total_rows} exterior rows (D4 symmetry used)')


def radical_gap_at_most(a: int, b: int, gap: F) -> bool:
    """Exact test |sqrt(a)-sqrt(b)| <= gap, for a,b>=0 and gap>=0."""
    assert a >= 0 and b >= 0 and gap >= 0
    left = a+b-gap*gap
    return left <= 0 or left*left <= 4*a*b


def check_integral_rotation_net():
    q = 65
    quadrant = [(65, 0), (63, 16), (60, 25), (56, 33), (52, 39),
                (39, 52), (33, 56), (25, 60), (16, 63), (0, 65)]
    rotations = {(sx*x, sy*y) for x, y in quadrant for sx in (-1, 1) for sy in (-1, 1)}
    assert len(rotations) == 36
    assert all(x*x+y*y == q*q for x, y in rotations)
    min_dot = min(a[0]*b[0]+a[1]*b[1] for a, b in zip(quadrant, quadrant[1:]))
    assert F(min_dot, q*q) == F(24, 25)
    # The half-gap squared chord is at most 2-7 sqrt(2)/5 < 1/49.
    # The last comparison is equivalent to 2*343^2 > 485^2.
    assert 2*343**2-485**2 == 73 > 0
    rng = random.Random(749181)
    for _ in range(1000):
        den = rng.randint(1, 1000)
        t = F(rng.randint(-1000, 1000), den)
        z = ((1-t*t)/(1+t*t), 2*t/(1+t*t))
        assert min(sqdist(z, (F(ux, q), F(uy, q))) for ux, uy in rotations) <= F(1, 49)
    assert F(1, 16)+(6+F(1, 16))/7 == F(13, 14) < 1

    representations = {}
    for x in range(-100, 101):
        for y in range(-100, 101):
            t = x*x+y*y
            if 0 < t <= 10000:
                representations.setdefault(t, (x, y))
    cases = [(16*q, (px*q, py*q))
             for px, py in ((32, 0), (40, 24), (-48, 16), (64, -32), (64, 64), (80, -48))]
    cases += [(1000, (2345, 987)), (1000, (5000, 3000))]
    endpoints = 0
    for L, p in cases:
        pnorm = sqdist(p, (0, 0))
        assert 4*L*L <= pnorm <= 36*L*L
        # Check that no relevant represented norm lies beyond the finite list.
        assert (isqrt(pnorm)+1+F(L, 16))**2 < q*q*10000
        expected_t = {t for t in representations
                      if radical_gap_at_most(q*q*t, pnorm, F(L, 16))}
        realized = set()
        for t in expected_t:
            x, y = representations[t]
            for ux, uy in rotations:
                a = (p[0]+ux*x-uy*y, p[1]+ux*y+uy*x)
                if sqdist(a, (0, 0)) <= L*L:
                    assert sqdist(a, p) == q*q*t
                    realized.add(t)
                    endpoints += 1
                    break
            else:
                raise AssertionError(('no exact lattice endpoint', p, t))
        assert realized == expected_t
    print(f'Integral rotation net and shifted-disk support realization: PASS '
          f'({len(rotations)} rotations of common modulus {q}, '
          f'1000 rational net tests, {endpoints} actual integer endpoint realizations)')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--quick', action='store_true', help='omit the largest finite grid checks')
    args = parser.parse_args()
    check_balanced_weights()
    check_witness_couplings()
    check_geometry()
    check_forced_stars()
    check_grid_edge_congestion(args.quick)
    check_full_grid_normalization(args.quick)
    check_integral_rotation_net()
    print('ALL EXACT WEIGHTED CROSS-DISTANCE CHECKS PASSED')


if __name__ == '__main__':
    main()
