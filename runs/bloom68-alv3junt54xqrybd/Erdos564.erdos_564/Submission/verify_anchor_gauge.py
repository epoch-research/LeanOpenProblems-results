#!/usr/bin/env python3
"""Exact checks for AnchorGaugeCounterexample.md (standard library only).

The probabilistic existence argument for the large blown-up 3-graphs is in
that note. This script independently checks a concrete 32-label base graph,
all occupancy patterns relevant to the collision bound, and the final exact
rational inequality. It does not modify or import any Lean helper.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import comb, factorial, log2

# Symmetric adjacency bitmasks of an explicitly chosen graph on 32 labels.
F = (
    0x0F748208, 0xBD8F0BD4, 0xECE2B0A2, 0x9E5C2E31,
    0xE059E60A, 0x8235764C, 0xD9F541A2, 0x91B00146,
    0x474A60C2, 0x131C743B, 0x378C0A38, 0x40CD040A,
    0x9946E224, 0x16D4D33C, 0x1449B370, 0xA0827015,
    0x1D0E4872, 0x01059106, 0x76033E6B, 0x08814F1A,
    0x724022F9, 0x1BC000E5, 0xF0B0795D, 0xE168ACC6,
    0x0EA317C3, 0x9D342729, 0xB305650F, 0xD329104F,
    0xCE7576CA, 0x84D48416, 0x98D40954, 0x7EC090FE,
)
N = len(F)


def pair_bit(i, j):
    return (F[i] >> j) & 1


def triple_bit(i, j, k):
    return pair_bit(i, j) ^ pair_bit(i, k) ^ pair_bit(j, k)


def clique_count(adj, remaining, size):
    """Count cliques of the requested size, each in increasing vertex order."""
    if size == 0:
        return 1
    if remaining.bit_count() < size:
        return 0
    answer = 0
    while remaining.bit_count() >= size:
        bit = remaining & -remaining
        remaining ^= bit
        vertex = bit.bit_length() - 1
        answer += clique_count(adj, remaining & adj[vertex], size - 1)
    return answer


def switching_clique_count(size):
    """Count sets on which delta F is constant, using their smallest anchor.

    With anchor v, delta F(v,i,j) is a graph colour on i,j. Since delta F
    is cocyclic, the full set is monochromatic iff this link graph is.
    """
    answer = 0
    all_vertices = (1 << N) - 1
    for v in range(N):
        adj = [0] * N
        for i in range(v + 1, N):
            for j in range(i + 1, N):
                if triple_bit(v, i, j):
                    adj[i] |= 1 << j
                    adj[j] |= 1 << i
        remaining = all_vertices ^ ((1 << (v + 1)) - 1)
        complement = [(remaining ^ row) & ~(1 << i)
                      for i, row in enumerate(adj)]
        answer += clique_count(adj, remaining, size - 1)
        answer += clique_count(complement, remaining, size - 1)
    return answer


def padded_partitions(total, parts, minimum=0):
    """All sorted nonnegative occupancy vectors, including unused blocks."""
    if parts == 1:
        if total >= minimum:
            yield (total,)
        return
    for first in range(minimum, total // parts + 1):
        for tail in padded_partitions(total - first, parts - 1, first):
            yield (first,) + tail


def verify_gauge_identity_small():
    """Exhaustively check the image/preimage identity on 3, 4, and 5 vertices."""
    for n in (3, 4, 5):
        pairs = list(combinations(range(n), 2))
        triples = list(combinations(range(n), 3))
        pair_indices = {edge: i for i, edge in enumerate(pairs)}
        triple_masks = [sum(1 << pair_indices[e] for e in combinations(t, 2))
                        for t in triples]
        images = Counter()
        for graph in range(1 << len(pairs)):
            image = sum(((graph & mask).bit_count() % 2) << i
                        for i, mask in enumerate(triple_masks))
            images[image] += 1
        assert len(images) == 2 ** comb(n - 1, 2)
        assert set(images.values()) == {2 ** (n - 1)}
        full = (1 << len(triples)) - 1
        quad_masks = []
        triple_indices = {edge: i for i, edge in enumerate(triples)}
        for quad in combinations(range(n), 4):
            quad_masks.append(sum(1 << triple_indices[e]
                                  for e in combinations(quad, 3)))
        for chi in range(1 << len(triples)):
            cocyclic = all((chi & mask).bit_count() % 2 == 0
                           for mask in quad_masks)
            mono_gauges = images[chi] + images[chi ^ full]
            expected = 2 ** n if cocyclic else 0
            assert mono_gauges == expected
    print("Gauge identity: exhaustive checks passed for n=3,4,5.")


def main():
    assert N == 32
    for i in range(N):
        assert pair_bit(i, i) == 0
        for j in range(N):
            assert pair_bit(i, j) == pair_bit(j, i)
    for quad in combinations(range(N), 4):
        assert sum(triple_bit(*edge) for edge in combinations(quad, 3)) % 2 == 0
    mono8 = switching_clique_count(8)
    mono9 = switching_clique_count(9)
    assert mono8 == 11 and mono9 == 0
    print(f"Explicit base graph: {mono8} monochromatic delta-F 8-sets; "
          f"{mono9} monochromatic delta-F 9-sets.")

    union_bound = Fraction(comb(32, 9), 2 ** 27)
    assert union_bound < 1
    print(f"Independent base-graph existence bound: {union_bound} < 1.")

    maximum = -1
    maximizer = None
    number = 0
    for occupancy in padded_partitions(33, 8):
        number += 1
        cross_triples = sum(occupancy[i] * occupancy[j] * occupancy[k]
                            for i, j, k in combinations(range(8), 3))
        if cross_triples > maximum:
            maximum, maximizer = cross_triples, occupancy
    assert number == 3828
    assert maximum == 3920
    assert maximizer == (4, 4, 4, 4, 4, 4, 4, 5)
    noisy_triples = comb(33, 3) - maximum
    assert noisy_triples == 1536
    print(f"All {number} sorted occupancy patterns checked: minimum "
          f"number of noisy triples = {noisy_triples}.")

    D = Fraction(factorial(32), 32 ** 32)
    raw_exponent = comb(32, 2) + 2 * comb(31, 2) - 2
    assert raw_exponent == 1424
    assert factorial(32) > 2 ** 117
    assert D > Fraction(1, 2 ** 43)
    p33_upper = Fraction(1, 2 ** noisy_triples)
    required_lower = Fraction(1, 2 ** raw_exponent) * D ** 2
    assert p33_upper < required_lower
    # The original, unsquared left side is >2^-507; its RHS is <=2^-520.
    assert Fraction(1, 2 ** 464) * D > Fraction(1, 2 ** 507)
    assert 248 - noisy_triples // 2 == -520
    gap_bits = noisy_triples - raw_exponent + 2 * log2(D)
    necessary_gauge_cost = noisy_triples - 928 + 2 * log2(D)
    print("Exact rational comparison passed: 2^-1536 < 2^-1424 (32!/32^32)^2.")
    print(f"Squared gap: {gap_bits:.9f} bits; "
          f"necessary gauge cost at n=32: at least {necessary_gauge_cost:.9f}.")
    verify_gauge_identity_small()


if __name__ == "__main__":
    main()
