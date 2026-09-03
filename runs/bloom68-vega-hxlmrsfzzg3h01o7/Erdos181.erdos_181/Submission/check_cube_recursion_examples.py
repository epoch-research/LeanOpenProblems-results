#!/usr/bin/env python3
"""Finite supplementary checks; the principal eight-vertex result is also Lean-proved."""
from fractions import Fraction
from itertools import combinations, permutations
import random


def edge(x, y):
    return tuple(sorted((x, y)))


def cube_edges(m):
    return {edge(x, x ^ (1 << i)) for x in range(2**m) for i in range(m)}


def four_cycles(vertex_count, edges):
    neighbors = [set() for _ in range(vertex_count)]
    for x, y in edges:
        neighbors[x].add(y)
        neighbors[y].add(x)
    return sum(len(neighbors[x] & neighbors[y]) * (len(neighbors[x] & neighbors[y]) - 1) // 2
               for x, y in combinations(range(vertex_count), 2)) // 2


# All noninduced spanning copies of Q3 have one of these 840 edge sets.
q3 = cube_edges(3)
labelled_cubes = {frozenset(edge(p[x], p[y]) for x, y in q3)
                 for p in permutations(range(8))}
assert len(labelled_cubes) == 840
red = {edge(x, y) for x, y in [(0, 1), (0, 3), (0, 5), (0, 6), (1, 2), (1, 4),
                              (2, 3), (2, 6), (3, 7), (4, 5), (4, 7), (5, 6), (6, 7)]}
blue = set(combinations(range(8), 2)) - red
assert all(not (q <= red) and not (q <= blue) for q in labelled_cubes)
assert {edge(x, y) for x, y in [(0, 1), (1, 2), (2, 3), (3, 0),
                               (4, 5), (5, 6), (6, 7), (7, 4)]} <= red
assert {(0, 5), (1, 4), (2, 6), (3, 7)} <= red
nb = lambda x: {y for y in range(8) if edge(x, y) in blue}
assert nb(0) == {2, 4, 7} and nb(6) == {1, 3, 4}
print('K8: two red squares plus a red perfect matching, but no cube in either color.')

# Test the proved-on-paper four-cycle identity for pure twisted cubes.
rng = random.Random(0)
for m in [2, 3]:
    q = cube_edges(m)
    N = 2**m
    ps = permutations(range(N)) if m == 2 else [rng.sample(range(N), N) for _ in range(100)]
    for p in ps:
        twisted = q | {(x + N, y + N) for x, y in q} | {(x, N + p[x]) for x in range(N)}
        preserved = sum(edge(p[x], p[y]) in q for x, y in q)
        assert four_cycles(2 * N, twisted) == 2 * four_cycles(N, q) + preserved
print('Twisted-cube four-cycle formula: all Q2 permutations and 100 fixed-sample Q3 permutations.')

# A cube of any tested dimension is a union of two C4-free graphs.
for m in range(2, 8):
    split = [set(), set()]
    for x, y in cube_edges(m):
        lower = x if x.bit_count() < y.bit_count() else y
        split[lower.bit_count() % 2].add((x, y))
    assert split[0] | split[1] == cube_edges(m)
    assert four_cycles(2**m, split[0]) == four_cycles(2**m, split[1]) == 0
print('Parity-of-lower-weight decomposition: both colors C4-free for dimensions 2,...,7.')

# Integer little-o-error counterexample.
x, harmonic = 1, Fraction(0)
for n in range(100):
    assert harmonic + Fraction(1, 2**n) <= Fraction(x, 2**n) <= 1 + harmonic
    x = 2 * x + 2**(n + 1) // (n + 1)
    harmonic += Fraction(1, n + 1)
print('Integer harmonic-growth recurrence bounds checked through n=99.')

# Sharp normalized halving recurrence with A=1 and a_1=0.
a = {1: Fraction(0)}
for n in range(2, 10001):
    a[n] = a[n // 2] + Fraction(1, n)
    assert a[n] <= 1 - Fraction(1, n)
print('Halving recurrence bound checked through n=10,000.')
