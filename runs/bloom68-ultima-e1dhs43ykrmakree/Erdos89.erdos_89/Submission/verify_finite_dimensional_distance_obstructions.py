#!/usr/bin/env python3
"""Exact audits for finite_dimensional_distance_obstructions.md.

The proofs are in the accompanying note.  These checks use integer/rational
arithmetic, squarefree-radical normal forms, and exact polynomial identities.
No numerical optimization, floating-point distance equality, or Lean edits.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement
from math import gcd

import numpy as np
import sympy as sp


def product_histogram(xs):
    one = Counter((x - y) ** 2 for x in xs for y in xs)
    two = Counter()
    for s, cs in one.items():
        for t, ct in one.items():
            if s + t:
                two[s + t] += cs * ct
    n = len(xs) ** 2
    assert sum(two.values()) == n * (n - 1)
    return two


def coherent_closure(points):
    """Exact stable ordered-pair (2-WL) refinement of distance colors."""
    n = len(points)
    dist = np.array(
        [[sum((a - b) ** 2 for a, b in zip(x, y)) for y in points]
         for x in points], dtype=np.int64)
    labels = {v: i for i, v in enumerate(sorted(set(dist.flat)))}
    colors = np.array([[labels[v] for v in row] for row in dist], dtype=np.int64)
    stages = []
    while True:
        new_labels = {}
        new_colors = np.empty((n, n), dtype=np.int64)
        for i in range(n):
            for j in range(n):
                counts = Counter(zip(map(int, colors[i, :]),
                                     map(int, colors[:, j])))
                signature = (int(colors[i, j]), tuple(sorted(counts.items())))
                if signature not in new_labels:
                    new_labels[signature] = len(new_labels)
                new_colors[i, j] = new_labels[signature]
        old_count = len(set(colors.flat))
        colors = new_colors
        stages.append(len(new_labels))
        if len(new_labels) == old_count:
            return dist, colors, stages


def d4_images(p):
    x, y = p
    return ((x, y), (x, -y), (-x, y), (-x, -y),
            (y, x), (y, -x), (-y, x), (-y, -x))


def orbital_signature(p, q):
    return min(zip(d4_images(p), d4_images(q)))


def audit_coherent_algebra():
    print('COHERENT-CLOSURE AUDITS (exact integer arithmetic)')
    for L in range(2, 8):
        xs = list(range(-(L - 1), L, 2))
        points = [(x, y) for x in xs for y in xs]
        n = L * L
        dist, colors, stages = coherent_closure(points)
        rank = len(set(colors.flat))
        diagonal_cells = Counter(colors.diagonal())
        expected_cells = Counter(tuple(sorted(map(abs, p))) for p in points)
        assert sorted(diagonal_cells.values()) == sorted(expected_cells.values())
        eps = L % 2
        exact_rank = (L ** 4 + 2 * (1 + eps) * L * L + 3 * eps) // 8
        assert rank == exact_rank
        assert len(diagonal_cells) == ((L + 1) // 2) * (((L + 1) // 2) + 1) // 2
        # All coherent relations have at most twice the largest fiber size.
        assert max(Counter(colors.flat).values()) <= 2 * max(diagonal_cells.values())
        D = len(set(dist.flat)) - 1
        assert rank * (4 * D + 2) >= n * n
        shortest = min(d for d in dist.flat if d > 0)
        shortest_adjacency = sp.Matrix((dist == shortest).astype(int))
        assert shortest_adjacency.rank() == L * L - L

        # Independently audit the explicit rank-two algebra identities.
        X = np.array(points, dtype=object)
        B = X @ X.T
        rho = np.array([x * x + y * y for x, y in points], dtype=object)
        u = np.array([x * x - y * y for x, y in points], dtype=object)
        v = np.array([2 * x * y for x, y in points], dtype=object)
        U = np.outer(u, u)
        T = 2 * (B * B) - np.outer(rho, rho)
        alpha = sum(a * a for a in u)
        gamma = sum(a * a for a in v)
        assert np.array_equal(T, U + np.outer(v, v))
        assert np.array_equal(T @ T - gamma * T, (alpha - gamma) * U)
        c = sum((x * x - y * y) * x * x for x, y in points)
        W = np.array([[u[i] * (x * z - y * w) for z, w in points]
                      for i, (x, y) in enumerate(points)], dtype=object)
        assert np.array_equal((U * B) @ B, c * W)
        if L >= 3:
            assert alpha != gamma and c > 0
            # The six constructed entry invariants separate all D4 orbitals.
            invariant_to_orbital = {}
            orbital_to_invariant = {}
            for i, p in enumerate(points):
                for j, q in enumerate(points):
                    signature = (rho[i], rho[j], u[i] ** 2, u[j] ** 2,
                                 B[i, j], W[i, j])
                    orbital = orbital_signature(p, q)
                    assert invariant_to_orbital.setdefault(signature, orbital) == orbital
                    assert orbital_to_invariant.setdefault(orbital, signature) == signature
            assert len(invariant_to_orbital) == exact_rank
        print(f'  L={L}: n={n}, D={D}, refinement ranks={stages}, '
              f'fibers={len(diagonal_cells)}, coherent dimension={rank}')

    # General radial-block counting, without any Cartesian/symmetry assumption.
    samples = [
        [(0, 0), (1, 0), (0, 2), (3, 1), (-2, 4), (5, -3)],
        [(i, (i * i + 3 * i) % 17) for i in range(12)],
        [(x, y) for x in range(4) for y in range(3)],
    ]
    for points in samples:
        n = len(points)
        dist, colors, _ = coherent_closure(points)
        row_sums = [int(x) for x in dist.sum(axis=1)]
        radial_sizes = Counter(row_sums)
        m = max(radial_sizes.values())
        D = len(set(dist.flat)) - 1
        blocks = Counter((row_sums[i], row_sums[j], int(dist[i, j]))
                         for i in range(n) for j in range(n))
        assert m <= 2 * D + 1
        assert max(blocks.values()) <= 2 * m
        assert len(blocks) * 2 * m >= n * n
        assert len(set(colors.flat)) >= len(blocks)
    print('  General radial-block bound checked on three nonsquare samples.')


def formal_gap_keys(m):
    coordinates = [(i, j) for i in range(m) for j in range(i, m)]

    def key(v):
        return tuple(v[i] * v[j] * (1 if i == j else 2)
                     for i, j in coordinates)

    result = [key([0] * m)]
    for i in range(m):
        v = [0] * m
        v[i] = 2
        result.append(key(v))
    for i in range(m):
        for j in range(i + 1, m):
            for sign in (-1, 1):
                v = [0] * m
                v[i], v[j] = 1, sign
                result.append(key(v))
    return result


def audit_formal_gap_uniqueness():
    print('\nFORMAL QUADRATIC-FORM UNIQUENESS')
    for m in range(2, 11):
        keys = formal_gap_keys(m)
        sums = [tuple(a + b for a, b in zip(x, y))
                for x, y in combinations_with_replacement(keys, 2)]
        assert len(sums) == len(set(sums))
        assert len(sums) - 1 == m * m * (m * m + 3) // 2
        print(f'  m={m}: {m*m} nonzero one-dimensional gap types, '
              f'{len(sums)-1} formal planar distance types; no collisions')


def squarefree_part(n):
    square, radical = 1, 1
    for p, exponent in sp.factorint(n).items():
        p, exponent = int(p), int(exponent)
        square *= p ** (exponent // 2)
        if exponent % 2:
            radical *= p
    assert square * square * radical == n
    return square, radical


def radical_key(d):
    return tuple(sorted((r, c) for r, c in d.items() if c))


def add_radicals(a, b):
    c = Counter(dict(a))
    c.update(dict(b))
    return radical_key(c)


def audit_explicit_moment_perturbation():
    print('\nEXPLICIT ALGEBRAIC 400-POINT PAIR')
    m, L = 10, 20
    base = [(2 * j + 1) ** 2 for j in range(m)]
    # z is perpendicular to both 1 and the baseline squared-coordinate vector.
    z = [0, 0, 2, -5, 11, 3, -7, 17, -13, 23]
    z[1] = -sum((base[j] - base[0]) * z[j] // 8 for j in range(2, m))
    z[0] = -sum(z[1:])
    w = [7 * a for a in z]
    w[0] -= 1
    w[1] += 1
    denominator = sum(a * a for a in w)
    numerators = [a * denominator - 16 * b for a, b in zip(base, w)]
    assert sum(w) == 0
    assert sum(a * b for a, b in zip(base, w)) == 8
    assert min(numerators) > 0
    assert numerators == sorted(numerators)
    assert len(set(numerators)) == m
    assert sum(numerators) == denominator * sum(base)
    assert sum(a * a for a in numerators) == denominator ** 2 * sum(a * a for a in base)
    # Perturbed positive coordinates are sqrt(numerators[i]/denominator).
    # A common denominator can be omitted in equality tests for squared gaps.
    radicals = [squarefree_part(a) for a in numerators]
    gaps = []
    for i in range(m):
        gaps.append((((1, 4 * numerators[i]),), 2))
    for i in range(m):
        for j in range(i + 1, m):
            ai, ri = radicals[i]
            aj, rj = radicals[j]
            g = gcd(ri, rj)
            factor, rad = ai * aj * g, ri * rj // (g * g)
            assert factor * factor * rad == numerators[i] * numerators[j]
            for sign in (-1, 1):
                coefficients = Counter({1: numerators[i] + numerators[j]})
                coefficients[rad] += sign * 2 * factor
                gaps.append((radical_key(coefficients), 4))
    # Distinct squarefree radicals are Q-linearly independent.
    assert len({k for k, c in gaps}) == m * m
    with_zero = [((), L)] + gaps
    histogram = Counter()
    for i, (a, ca) in enumerate(with_zero):
        for j in range(i, len(with_zero)):
            if i == j == 0:
                continue
            b, cb = with_zero[j]
            histogram[add_radicals(a, b)] += ca * cb * (1 if i == j else 2)
    n = L * L
    D = len(histogram)
    E = sum(c * c for c in histogram.values())
    expected_D = m * m * (m * m + 3) // 2
    expected_E = 48 * L ** 4 - 120 * L ** 3 + 8 * L * L + 120 * L
    assert sum(histogram.values()) == n * (n - 1)
    assert () not in histogram
    assert D == expected_D and E == expected_E
    assert max(histogram.values()) == 8 * L
    grid = product_histogram(list(range(-(L - 1), L, 2)))
    grid_D, grid_E = len(grid), sum(c * c for c in grid.values())
    mu2 = Fraction(sum(base), m)
    mu4 = Fraction(sum(a * a for a in base), m)
    S = 2 * n * mu2
    T = 2 * n * (mu4 + mu2 * mu2)
    assert T * n > S * S
    assert mu4 - 3 * mu2 * mu2 != 0
    coherent_dimension = (n * n + 2 * n) // 8
    print(f'  denominator={denominator}')
    print(f'  numerators={numerators}')
    print('  Both first two power sums of squared positive coordinates match exactly.')
    print(f'  Grid:      (n,D,E)=({n},{grid_D},{grid_E})')
    print(f'  Perturbed: (n,D,E)=({n},{D},{E})')
    print(f'  Common EDM parameters S={S}, T={T}; spectrum '
          '{-S,-S,S+sqrt(nT),S-sqrt(nT),0^(n-4)}.')
    print(f'  Common unlabelled coherent algebra has dimension {coherent_dimension}, '
          f'and a full M_{m*(m+1)//2}(R) corner.')


def hilbert_count(L, k):
    return sum(a + b <= k for a in range(L) for b in range(L))


def audit_hilbert_functions():
    print('\nHILBERT-FUNCTION AUDITS')
    for xs in ([Fraction(-3), Fraction(-1), Fraction(1), Fraction(3)],
               [Fraction(-7, 2), Fraction(-2, 3), Fraction(2, 3), Fraction(7, 2)]):
        L = len(xs)
        pts = [(x, y) for x in xs for y in xs]
        for k in range(2 * L):
            monomials = [(a, d - a) for d in range(k + 1) for a in range(d + 1)]
            V = sp.Matrix([[x ** a * y ** b for a, b in monomials] for x, y in pts])
            assert V.rank() == hilbert_count(L, k)
    print('  Two different exact rational Cartesian products have the asserted ranks at every degree through saturation.')
    ks = (0, 1, 2, 5, 10, 19, 20, 25, 37, 38, 39)
    print('  L=20 full formula sample:', [(k, hilbert_count(20, k)) for k in ks])


def newton_power_sums(poly, q):
    coefficients = poly.all_coeffs()
    assert coefficients[0] == 1
    values = [poly.degree()]
    for k in range(1, q + 1):
        values.append(-k * coefficients[k]
                      - sum(coefficients[j] * values[k - j] for j in range(1, k)))
    return values


def audit_high_order_moment_matching():
    print('\nHIGH-ORDER EXACT MOMENT/GRAM AUDITS')
    t = sp.symbols('t')
    for K in (2, 3):
        q, m = 2 * K, 2 * K + 8
        L = 2 * m
        roots = [(2 * j + 1) ** 2 for j in range(m)]
        original = sp.Poly(sp.prod(t - r for r in roots), t)
        perturbed = original + sp.Poly(sum(t ** j for j in range(8)), t)
        assert original.all_coeffs()[:q + 1] == perturbed.all_coeffs()[:q + 1]
        # Exact sign changes on disjoint positive intervals certify all m roots
        # of the perturbed polynomial are real, simple, and positive.
        for r in roots:
            left, right = sp.Rational(r) - sp.Rational(1, 10), sp.Rational(r) + sp.Rational(1, 10)
            assert left > 0
            assert perturbed.eval(left) * perturbed.eval(right) < 0
        powers0 = [m] + [sum(r ** j for r in roots) for j in range(1, q + 1)]
        powers1 = newton_power_sums(perturbed, q)
        assert powers0 == powers1
        features = [(a, d - a) for d in range(2 * K + 1) for a in range(d + 1)]

        def moment(powers, k):
            return 0 if k % 2 else 2 * powers[k // 2]

        def gram(powers):
            return sp.Matrix([[moment(powers, a + c) * moment(powers, b + d)
                               for c, d in features] for a, b in features])

        G0, G1 = gram(powers0), gram(powers1)
        assert G0 == G1
        assert G0.rank() == len(features)
        # Check the universal two-sided polynomial feature representation.
        x, y, z, w = sp.symbols('x y z w')
        index = {ab: i for i, ab in enumerate(features)}
        for k in range(K + 1):
            poly = sp.Poly(((x - z) ** 2 + (y - w) ** 2) ** k, x, y, z, w)
            C = sp.zeros(len(features))
            for (a, b, c, d), coefficient in poly.terms():
                C[index[a, b], index[c, d]] += coefficient
            assert C == C.T
            vx = sp.Matrix([x ** a * y ** b for a, b in features])
            vz = sp.Matrix([z ** a * w ** b for a, b in features])
            assert sp.expand((vx.T * C * vz)[0] - poly.as_expr()) == 0
        print(f'  K={K}, L={L}: {m} positive algebraic roots certified; '
              f'moments through degree {4*K} and {len(features)}x{len(features)} feature Grams agree exactly.')
    print('  These explicit polynomial samples audit moment matching, not the generic distance-count assertion;')
    print('  the latter is proved by the local-surjectivity lemma and audited separately above.')


def main():
    audit_coherent_algebra()
    audit_formal_gap_uniqueness()
    audit_explicit_moment_perturbation()
    audit_hilbert_functions()
    audit_high_order_moment_matching()
    print('\nALL EXACT CHECKS PASSED.')


if __name__ == '__main__':
    main()
