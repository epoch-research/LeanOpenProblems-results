"""Exact finite checks for JointGapScaleAttempt.md; not a prime-existence test."""
from fractions import Fraction as F
from itertools import product
from math import comb


def has_cross_group_chain(counts, m):
    labels = [i for i, count in enumerate(counts) for _ in range(count)]
    return any(len(set(labels[j:j + m + 1])) == m + 1
               for j in range(len(labels) - m))


occupancy_cases = 0
for length in range(8):
    for counts in product(range(4), repeat=length):
        total = sum(counts)
        pairs = sum(comb(v, 2) for v in counts)
        for m in range(2, 6):
            if total - m * pairs > m:
                assert has_cross_group_chain(counts, m), (counts, m)
            occupancy_cases += 1

A = F(399, 100)
for m in range(2, 501):
    threshold = 2 * A * m * m
    M = threshold.numerator // threshold.denominator + 1
    u = 2 * m
    main = u - m - A * m * u * u / (2 * M)
    assert main > 0
    M_safe = 8 * m * m
    assert u - m - A * m * u * u / (2 * M_safe) == F(m, 400)
    for scale in [1, 2, 7, 40]:
        K = M * scale
        actual_pairs = M * comb(K // M, 2)
        assert actual_pairs == F(K * K, 2) * (F(1, M) - F(1, K))

span_cases = 0
# Arbitrary increasing finite point sets; no primality assumption or search.
for mask in range(1 << 12):
    points = [i for i in range(12) if (mask >> i) & 1]
    if len(points) < 2:
        continue
    adjacent = [y - x for x, y in zip(points, points[1:])]
    for m in range(1, min(5, len(points))):
        spans = [points[j + m] - points[j]
                 for j in range(len(points) - m)]
        assert sum(spans) <= m * (points[-1] - points[0])
        for h in range(13):
            pair_count = sum(y - x <= h
                             for j, x in enumerate(points)
                             for y in points[j + 1:])
            short_span_count = sum(s <= h for s in spans)
            assert m * short_span_count <= pair_count
            bad_min_count = sum(min(adjacent[j:j + m]) <= h
                                for j in range(len(points) - m))
            short_gap_count = sum(d <= h for d in adjacent)
            assert bad_min_count <= m * short_gap_count <= m * pair_count
            span_cases += 1

print(f"PASS: {occupancy_cases:,} occupancy/m cases; 499 chain thresholds; "
      f"{span_cases:,} finite span/pair/minimum cases.")
