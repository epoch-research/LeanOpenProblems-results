#!/usr/bin/env python3
"""Exact verification of two explicit cube-trade constructions. No search/LP.

The proofs are in the accompanying Lean files. This independently checks the
fixed constructions, every intersection, every capacity, and every row pair.
"""
from collections import Counter
from itertools import combinations
from math import prod


def subsets(items):
    items = tuple(sorted(items))
    return [frozenset(c) for r in range(len(items) + 1)
            for c in combinations(items, r)]


def moments(histogram, patterns):
    return {s: sum(n for t, n in histogram.items() if s <= t)
            for s in patterns}


def verify(length, primes, tops, expected):
    primes = frozenset(primes)
    tops = tuple(map(frozenset, tops))
    patterns = subsets(primes)
    empty = frozenset()
    baseline = Counter(frozenset(p for p in primes if n % p == 0)
                       for n in range(1, length + 1))
    base_moments = moments(baseline, patterns)
    assert all(base_moments[s] == length // prod(s) for s in patterns)
    assert len(tops) == len(set(tops)) == baseline[empty]
    assert all(r <= primes and len(r) % 2 == 1 for r in tops)
    assert all(length % prod(r) != 0 for r in tops)

    # Exact even-pattern capacities, including the empty pattern.
    loads = {t: sum(t <= r for r in tops) for t in patterns}
    assert all(loads[t] <= baseline[t] for t in patterns if len(t) % 2 == 0)

    changed = baseline.copy()
    for r in tops:
        for t in subsets(r):
            changed[t] += (-1) ** (len(t) + 1)
    assert all(n >= 0 for n in changed.values())
    assert changed[empty] == 0 and sum(changed.values()) == length
    changed = Counter({t: n for t, n in changed.items() if n})
    expected = Counter({frozenset(t): n for t, n in expected.items()})
    assert changed == expected

    counts = moments(changed, patterns)
    for s in patterns:
        denominator = prod(s)
        floor = length // denominator
        ceil = (length + denominator - 1) // denominator
        assert counts[s] in {floor, ceil}
        assert counts[s] == base_moments[s] + int(s in tops)

    # Full integer Möbius inversion, not a fractional or truncated LP.
    inverse = {
        t: sum((-1) ** (len(s) - len(t)) * counts[s]
               for s in patterns if t <= s)
        for t in patterns
    }
    assert all(inverse[t] == changed[t] for t in patterns)
    rows = [t for t, n in changed.items() for _ in range(n)]
    assert len(rows) == length and all(rows)
    assert all(prod(a & b) < length for a, b in combinations(rows, 2))

    print(f'L={length}, P={sorted(primes)}, k={len(primes)}: verified')
    print('  histogram:', {tuple(sorted(t)): n for t, n in changed.items()})
    print('  all intersections:', {tuple(sorted(s)): counts[s] for s in patterns})
    return counts


def main():
    c19 = verify(19, (2, 3, 5, 7), ((2,), (3,), (5,), (7,), (2, 3, 5)), {
        (2,): 6, (3,): 4, (5,): 3, (7,): 2,
        (2, 3): 2, (2, 7): 1, (2, 3, 5): 1,
    })
    verify(11, (2, 3, 5), ((2,), (3,), (5,)), {
        (2,): 4, (3,): 3, (5,): 2, (2, 3): 1, (2, 5): 1,
    })
    # Since 19 = 3*6+1, the only residues giving maximal counts modulo 2
    # and 3 in [0,19) are both zero. Their joint count is four, not three.
    actual2 = {n for n in range(19) if n % 2 == 0}
    actual3 = {n for n in range(19) if n % 3 == 0}
    assert len(actual2) == c19[frozenset((2,))] == 10
    assert len(actual3) == c19[frozenset((3,))] == 7
    assert len(actual2 & actual3) == 4 != c19[frozenset((2, 3))] == 3
    print('CRT rounding incompatibility verified; no asymptotic claim made.')


if __name__ == '__main__':
    main()
