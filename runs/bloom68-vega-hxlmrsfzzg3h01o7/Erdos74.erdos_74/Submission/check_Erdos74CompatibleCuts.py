#!/usr/bin/env python3
"""Finite consistency checks for Erdos74CompatibleCuts.md (standard library)."""
from itertools import combinations, product
from math import isqrt
from random import Random


def constraints(lengths, L, odd_only=False):
    return [((1 << i) | (1 << j), (lengths[i] + lengths[j]) % 2)
            for i, j in combinations(range(len(lengths)), 2)
            if lengths[i] + lengths[j] <= L
            and (not odd_only or (lengths[i] + lengths[j]) % 2)]


def minimum_parities(lengths, L, odd_only=False):
    checks = constraints(lengths, L, odd_only)
    best = len(lengths) + 1
    minimizers = []
    for y in range(1 << len(lengths)):
        weight = y.bit_count()
        if weight > best:
            continue
        if all((y & mask).bit_count() % 2 == rhs for mask, rhs in checks):
            if weight < best:
                best, minimizers = weight, []
            minimizers.append(y)
    return best, minimizers


def formula(lengths, L):
    active = [i for i, n in enumerate(lengths) if n + 2 <= L]
    even = sum(lengths[i] % 2 == 0 for i in active)
    odd = len(active) - even
    return min(even, odd), active, even, odd


def build_theta(lengths):
    # Terminals are 0 and 1. Paths are stored as edge-index lists.
    edges, paths, next_vertex = [], [], 2
    for length in lengths:
        vertices = [0] + list(range(next_vertex, next_vertex + length - 1)) + [1]
        next_vertex += length - 1
        path = []
        for a, b in zip(vertices, vertices[1:]):
            path.append(len(edges))
            edges.append((a, b))
        paths.append(path)
    return next_vertex, edges, paths


def full_edge_support_minimum(lengths, L):
    _, edges, paths = build_theta(lengths)
    cycle_checks = []
    for i, j in combinations(range(len(lengths)), 2):
        if lengths[i] + lengths[j] <= L:
            cycle_mask = sum(1 << e for e in paths[i] + paths[j])
            cycle_checks.append((cycle_mask, (lengths[i] + lengths[j]) % 2))
    best = len(edges) + 1
    for support in range(1 << len(edges)):
        weight = support.bit_count()
        if weight >= best:
            continue
        if all((support & mask).bit_count() % 2 == rhs
               for mask, rhs in cycle_checks):
            best = weight
    return best


def run():
    rng = Random(7403)
    cases = [[2, 3, 3], [2, 3, 4], [2, 3, 3, 6, 6, 6, 6]]
    for _ in range(120):
        cases.append([2] + [rng.randint(3, 20) for _ in range(rng.randint(1, 8))])
    checked_scales = 0
    forced_phase_checks = 0
    for lengths in cases:
        for L in range(3, 2 * max(lengths) + 1):
            actual, minimizers = minimum_parities(lengths, L)
            predicted, active, even, odd = formula(lengths, L)
            assert actual == predicted, (lengths, L, actual, predicted)
            checked_scales += 1
            if even and odd and even != odd:
                majority = int(odd > even)
                expected = sum(1 << i for i in active
                               if lengths[i] % 2 != majority)
                assert minimizers == [expected], (lengths, L, minimizers, expected)
                assert (expected & 1) == majority
                forced_phase_checks += 1
    print(f"PASS: {checked_scales} exhaustive path-parity minima; "
          f"{forced_phase_checks} forced-majority phase checks")

    edge_cases = [[2, 3], [2, 3, 3], [2, 3, 4], [2, 3, 3, 4]]
    edge_scales = 0
    for lengths in edge_cases:
        for L in range(3, 2 * max(lengths) + 1):
            assert full_edge_support_minimum(lengths, L) == formula(lengths, L)[0]
            edge_scales += 1
    print(f"PASS: {edge_scales} original-edge support enumerations "
          "agree with parity compression")

    lengths = [2, 3, 3, 6, 6, 6, 6]
    assert minimum_parities(lengths, 5) == (1, [1])
    assert minimum_parities(lengths, 8) == (2, [0b110])
    assert minimum_parities(lengths, 8, odd_only=True)[0] == 1
    print("PASS: the jump from a_7=1 to a_8=2 requires the even-cycle checks")
    assert minimum_parities(lengths, 7)[0] == 1

    lengths = [2] + [3] * 2 + [6] * 4 + [9] * 8
    roots = []
    costs = []
    for L in [5, 8, 11]:
        best, minimizers = minimum_parities(lengths, L)
        roots.append({y & 1 for y in minimizers})
        costs.append(best)
    assert roots == [{1}, {0}, {1}]
    assert costs == [1, 2, 5]
    print("PASS: forced alternating parity on the fixed root path "
          "at three successive scales")

    # Enumerate all actual vertex two-colourings, fixing terminal u to zero.
    lengths = [2, 3, 3, 4, 4, 4]
    n, edges, paths = build_theta(lengths)
    core5 = sum(1 << e for path in paths[:3] for e in path)
    core6 = (1 << len(edges)) - 1
    best5 = best6 = len(edges) + 1
    for colour_mask in range(0, 1 << n, 2):
        bad = 0
        for e, (u, v) in enumerate(edges):
            if ((colour_mask >> u) ^ (colour_mask >> v)) & 1 == 0:
                bad |= 1 << e
        d = (colour_mask >> 1) & 1
        for length, path in zip(lengths, paths):
            assert sum((bad >> e) & 1 for e in path) % 2 == (length + d) % 2
        b5, b6 = (bad & core5).bit_count(), (bad & core6).bit_count()
        assert not (b5 == 1 and b6 == 2)
        assert b5 >= (2 if d == 0 else 1)
        assert b6 >= (2 if d == 0 else 4)
        best5, best6 = min(best5, b5), min(best6, b6)
    assert (best5, best6) == (1, 2)
    print(f"PASS: all {1 << (n - 1)} actual cuts satisfy the path identity; "
          "no cut minimizes both short-cycle cores")

    # Check the finite-ensemble scheduling, with compressed path counts.
    # Here h(L)=floor(sqrt(L)), phi(L)=2L+3, and B(L)=L+1.
    counts = []
    records = []
    previous_L = 4
    stage = 0
    for dimension in range(1, 4):
        while len(counts) < dimension:
            counts.append([1, 0])  # One even root path in the new lobe.
        for target in product((0, 1), repeat=dimension):
            stage += 1
            old_total = sum(sum(pair) for pair in counts)
            L = max(6, 2 * previous_L + 5, old_total ** 2 + 1)
            batch_size = max(stage * old_total, L + 1) + 1
            events = {}
            for i, parity in enumerate(target):
                length = L - 2 if L % 2 == parity else L - 3
                activation = length + 2
                assert activation > 2 * previous_L + 3
                events.setdefault(activation, []).append((i, parity))
            for activation, batch_locations in sorted(events.items()):
                for i, parity in batch_locations:
                    counts[i][parity] += batch_size
                actual = sum(min(pair) for pair in counts)
                assert actual <= old_total <= isqrt(activation)
            frozen = tuple(tuple(pair) for pair in counts)
            actual = sum(min(pair) for pair in frozen)
            assert all(frozen[i][bit] > frozen[i][1 - bit]
                       for i, bit in enumerate(target))
            for terminal_bits in product((0, 1), repeat=dimension):
                cost = sum(frozen[i][1 - bit] for i, bit in enumerate(terminal_bits))
                if terminal_bits == target:
                    assert cost == actual
                else:
                    assert cost >= batch_size > max(L + 1, stage * max(1, actual))
            records.append((dimension, stage, L, target, actual, frozen))
            previous_L = L
    assert len(records) == 14
    full_round = [record for record in records if record[0] == 3]
    terminal_vectors = list(product((0, 1), repeat=3))
    checked_families = 0
    for family_size in range(1, 8):
        for family in combinations(terminal_vectors, family_size):
            good_witness = False
            for _, j, L, target, actual, frozen in full_round:
                threshold = max(L + 1, j * max(1, actual))
                if all(sum(frozen[i][1 - bit] for i, bit in enumerate(bits))
                       > threshold for bits in family):
                    good_witness = True
                    break
            assert good_witness
            checked_families += 1
    assert checked_families == 254
    print(f"PASS: all activation budgets in {len(records)} ensemble stages; "
          f"all {checked_families} proper nonempty terminal-phase families "
          "have a simultaneous bad scale")

    print("These are finite checks, not a solution of Erdős 74.")


if __name__ == '__main__':
    run()
