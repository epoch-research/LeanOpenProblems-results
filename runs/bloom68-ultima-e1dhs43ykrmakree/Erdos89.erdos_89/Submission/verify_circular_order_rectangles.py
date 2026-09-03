#!/usr/bin/env python3
"""Exact sanity checks for the rectangular-grid AP counterexample.

These checks validate finite geometric/counting lemmas, not the asymptotic
counterexample by numerical extrapolation. All circular orders and arc tests
use integer determinants. No floating-point angular sorting is used.
"""
from collections import Counter, defaultdict
from functools import cmp_to_key
from math import gcd, isqrt


def polar_compare(a, b):
    def half(v):
        return 0 if v[1] > 0 or (v[1] == 0 and v[0] > 0) else 1
    ha, hb = half(a), half(b)
    if ha != hb:
        return -1 if ha < hb else 1
    cross = a[0] * b[1] - a[1] * b[0]
    if cross:
        return -1 if cross > 0 else 1
    return 0


def full_arc_graph(L, H):
    points = [(x, y) for x in range(L) for y in range(H)]
    n = len(points)
    energy_counts = Counter()
    multiplicities = Counter()
    arcs = []
    F = 0
    reflection_checks = 0
    narrow_checks = 0
    for pidx, p in enumerate(points):
        fibers = defaultdict(list)
        for qidx, q in enumerate(points):
            if qidx == pidx:
                continue
            dx, dy = q[0] - p[0], q[1] - p[1]
            fibers[dx * dx + dy * dy].append((dx, dy, qidx))
        F += len(fibers)
        for s, fiber in fibers.items():
            k = len(fiber)
            energy_counts[s] += k
            chosen = []
            if k == 2:
                chosen = [(fiber[0], fiber[1])]
            elif k >= 3:
                ordered = sorted(fiber, key=cmp_to_key(polar_compare))
                for i, a in enumerate(ordered):
                    b = ordered[(i + 1) % k]
                    cross = a[0] * b[1] - a[1] * b[0]
                    if cross == 0:
                        assert a[0] * b[0] + a[1] * b[1] < 0
                    if cross >= 0:  # cyclic angular gap <= pi
                        chosen.append((a, b))
            assert k - 1 <= len(chosen) <= k
            horizontal_count = 0
            for a, b in chosen:
                aidx, bidx = a[2], b[2]
                endpoint_pair = tuple(sorted((aidx, bidx)))
                multiplicities[endpoint_pair] += 1
                arcs.append((pidx, s, aidx, bidx))
                horizontal = a[1] == b[1]
                horizontal_count += horizontal
                if a[0] * b[0] < 0:
                    reflection_checks += 1
                    assert horizontal, (L, H, p, a, b, s)
                if s >= 4 * H * H and not horizontal:
                    narrow_checks += 1
                    assert a[0] * b[0] > 0
                    assert (a[0] - b[0]) ** 2 * s <= H ** 4
            assert horizontal_count <= 2
    D = len(energy_counts)
    E = sum(r * r for r in energy_counts.values())
    assert sum(energy_counts.values()) == n * (n - 1)
    assert n * (n - 1) - F <= len(arcs) <= n * (n - 1)
    assert F <= n * D
    assert sum(multiplicities.values()) == len(arcs)
    assert sum(1 for _, _, a, b in arcs if points[a][1] == points[b][1]) <= 2 * F
    return points, arcs, multiplicities, energy_counts, E, reflection_checks, narrow_checks


def independent_energy_check(L, H, actual_counts, E, check_parameterization):
    n = L * H
    by_norm = defaultdict(list)
    weighted = Counter()
    for x in range(-(L - 1), L):
        for y in range(-(H - 1), H):
            s = x * x + y * y
            by_norm[s].append((x, y))
            if s:
                weighted[s] += (L - abs(x)) * (H - abs(y))
    assert weighted == actual_counts
    Q = sum(len(vs) ** 2 for vs in by_norm.values())
    assert E <= n * n * Q
    parameter_checks = 0
    if check_parameterization:
        for vs in by_norm.values():
            for z in vs:
                for w in vs:
                    u = (z[0] + w[0], z[1] + w[1])
                    v = (z[0] - w[0], z[1] - w[1])
                    assert u[0] * v[0] + u[1] * v[1] == 0
                    if not all(u) or not all(v):
                        continue
                    q = gcd(abs(u[0]), abs(u[1]))
                    a, b = u[0] // q, u[1] // q
                    assert v[1] % a == 0
                    r = v[1] // a
                    assert r and v == (-r * b, r * a)
                    assert 1 <= abs(a) <= 2 * H
                    assert 1 <= abs(b) <= 2 * H
                    parameter_checks += 1
    # Direct integer version of the primitive-direction upper count.
    nonaxis_upper = 0
    for a in range(1, 2 * H + 1):
        for b in range(1, 2 * H + 1):
            nonaxis_upper += min((2 * L) // a, (2 * H) // b) * min(
                (2 * L) // b, (2 * H) // a)
    degenerate_upper = 2 * (4 * L + 1) * (4 * H + 1) + 32 * L * H
    assert Q <= degenerate_upper + 8 * nonaxis_upper
    return Q, parameter_checks


def capped_mass_checks(L, H, points, arcs, multiplicities):
    n = L * H
    total_checks = 0
    results = []
    for K in (1, 4, 9, 16):
        root = isqrt(K)
        T = 2 * H * root
        near = 0
        far_pairs = set()
        for _, s, a, b in arcs:
            if s < T * T:
                near += 1
            else:
                far_pairs.add(tuple(sorted((a, b))))
                if points[a][1] != points[b][1]:
                    assert abs(points[a][0] - points[b][0]) * T <= H * H
        actual = sum(min(mu, K) for mu in multiplicities.values())
        assert actual <= near + K * len(far_pairs)
        assert near <= 3 * n * H * T
        horizontal_capacity = H * L * (L - 1) // 2
        narrow_capacity = n * H * (2 * (H * H // T) + 1) // 2
        assert len(far_pairs) <= horizontal_capacity + narrow_capacity
        # Equation (5), multiplied by T to stay integral.
        assert actual * T <= 3 * n * H * T * T + K * n * L * T + K * n * H ** 3
        # Stronger 13/2 coefficient preceding the stated constant 7.
        assert 2 * actual <= 13 * n * H * H * root + 2 * K * n * L
        total_checks += 1
        results.append(actual)
    return total_checks, results


def main():
    cases = [(3, 3), (4, 3), (7, 4), (11, 5), (17, 3),
             (25, 6), (37, 7), (81, 4), (121, 3)]
    reflections = narrows = parameters = caps = total_arcs = 0
    print('Exact integer full-fiber checks; not an asymptotic numerical test.')
    print('L H n D arc_mass E Q M_1 M_4 M_9 M_16')
    for L, H in cases:
        points, arcs, mu, counts, E, rchecks, nchecks = full_arc_graph(L, H)
        Q, pchecks = independent_energy_check(L, H, counts, E, L <= 17)
        cchecks, values = capped_mass_checks(L, H, points, arcs, mu)
        print(L, H, L * H, len(counts), len(arcs), E, Q, *values)
        reflections += rchecks
        narrows += nchecks
        parameters += pchecks
        caps += cchecks
        total_arcs += len(arcs)
    print(f'PASS: {len(cases)} complete rectangles, {total_arcs} actual retained arcs, '
          f'{reflections} opposite-side checks, {narrows} large-radius narrow checks, '
          f'{parameters} nonaxis orthogonal parameter checks, {caps} cap/cutoff checks.')
    print('The asymptotic AP counterexample is proved in the accompanying note; '
          'these finite checks are only sanity checks of its lemmas.')


if __name__ == '__main__':
    main()
