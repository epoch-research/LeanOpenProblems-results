#!/usr/bin/env python3
"""Exact checks for contraction_scale_analysis.md.

These checks do not prove unrestricted contraction. All coordinates, norms,
coefficients, and direction comparisons below use integers or exact fractions.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import combinations, product
from math import isqrt
import random


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def sub(x, y):
    return x[0] - y[0], x[1] - y[1]


def scale(c, x):
    return c*x[0], c*x[1]


def cmul(x, y):
    return x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0]


def dot(x, y):
    return x[0]*y[0]+x[1]*y[1]


def norm2(x):
    return dot(x, x)


def poly(x, y):
    u, v = sub(x[0], y[0]), sub(x[1], y[1])
    return norm2(u), 2*dot(u, v), norm2(v)


def direction(x, y):
    u, v = sub(x[0], y[0]), sub(x[1], y[1])
    q = norm2(v)
    if not q:
        return None  # The vertical complex direction.
    return Fraction(dot(u, v), q), Fraction(u[1]*v[0]-u[0]*v[1], q)


def evaluate(f, M):
    return f[0]+M*f[1]+M*M*f[2]


def point(x, M):
    return add(x[0], scale(M, x[1]))


def distance_set(P):
    return {norm2(sub(x, y)) for x, y in combinations(P, 2)}


def D(P):
    return len(distance_set(P))


def diameter2(P):
    return max(distance_set(list(set(P))), default=0)


def parameters(S):
    A2 = diameter2([x[0] for x in S])
    B2 = diameter2([x[1] for x in S])
    ceilAB = isqrt(A2*B2)
    if ceilAB*ceilAB < A2*B2:
        ceilAB += 1
    M = 1 + max(A2, 4*ceilAB)
    return A2, B2, M


def check_direction_and_recovery(S):
    assert len(set(S)) == len(S)
    T = {poly(x, y) for x, y in combinations(S, 2)}
    assert (0, 0, 0) not in T
    max_pin_dirs = max_pin_polys = 0
    all_dirs = set()
    for x in S:
        by_poly = defaultdict(set)
        for y in S:
            if x == y:
                continue
            f, w = poly(x, y), direction(x, y)
            by_poly[f].add(w)
            all_dirs.add(w)
            if w is not None:
                assert w[0] == Fraction(f[1], 2*f[2])
                assert w[0]**2+w[1]**2 == Fraction(f[0], f[2])
        assert all(len(ws) <= 2 for ws in by_poly.values())
        nd = len(set().union(*by_poly.values()))
        assert nd <= 2*len(by_poly)
        max_pin_dirs = max(max_pin_dirs, nd)
        max_pin_polys = max(max_pin_polys, len(by_poly))
    assert len(all_dirs) <= 2*len(T)
    A2, B2, M = parameters(S)
    assert M > A2 and M*M > 16*A2*B2
    P = [point(x, M) for x in S]
    assert len(set(P)) == len(S)
    values = {evaluate(f, M) for f in T}
    assert len(values) == len(T)
    assert 0 not in values
    assert values == distance_set(P)
    # Check the bounded-multiplicity statement under only M>A^2.
    M0 = A2+1
    by_value = defaultdict(list)
    for f in T:
        by_value[evaluate(f, M0)].append(f)
    L = 1 + isqrt((16*A2*B2)//(M0*M0))
    assert max(map(len, by_value.values())) <= L
    assert len({point(x, M0) for x in S}) == len(S)
    return len(T), len(all_dirs), max_pin_polys, max_pin_dirs, M


rng = random.Random(238907)
A = list(product(range(3), repeat=2))
B = list(product(range(4), repeat=2))
universe = list(product(A, B))
for n in (4, 8, 16, 32, 64, 128, 144):
    S = rng.sample(universe, n)
    print('Direction/recovery:', n, check_direction_and_recovery(S))

# Genuinely unequal fibers with no common fine point.
fibers = {
    (0, 0): {(0, 0), (1, 2), (3, -1)},
    (1, 0): {(7, 4)},
    (0, 2): {(-2, 6), (4, 5)},
    (2, 1): {(5, -3), (5, -2), (7, -2), (8, -1)},
}
assert not set.intersection(*fibers.values())
S = [(a, b) for b, Ab in fibers.items() for a in Ab]
print('Unequal unanchored fibers:', len(S), check_direction_and_recovery(S))

# Complex-collinear exception: a=lambda*b+mu. Every evaluation is a similarity.
lam, mu = (1, 2), (3, -2)
S = [(add(cmul(lam, b), mu), b) for b in B]
T = {poly(x, y) for x, y in combinations(S, 2)}
assert len({direction(x, y) for x, y in combinations(S, 2)}) == 1
assert len(T) == D(B)
for M in (-10, -1, 0, 1, 10, 100):
    P = [point(x, M) for x in S]
    factor = norm2(add((M, 0), lam))
    assert factor > 0
    assert distance_set(P) == {factor*d for d in distance_set(B)}
print('Complex-collinear similarity exception: exact checks passed.')


def check_layer_cake(fibers, anchor=None):
    S = [(a, b) for b, Ab in fibers.items() for a in Ab]
    n = len(S)
    _, _, M = parameters(S)
    P = {point(x, M) for x in S}
    assert len(P) == n
    sizes = sorted((len(Ab) for Ab in fibers.values()), reverse=True)
    m1, m2 = sizes[:2]
    assert m1 >= 2
    bstar = max(fibers, key=lambda b: len(fibers[b]))
    Astar = fibers[bstar]
    levels = [{b for b, Ab in fibers.items() if len(Ab) >= j}
              for j in range(1, m2+1)]
    lower = D(Astar)+sum(D(Bj) for Bj in levels)
    assert D(P) >= lower
    assert len(Astar)+sum(len(Bj) for Bj in levels) == n+m2
    R = max([Fraction(len(Astar), D(Astar))]
            + [Fraction(len(Bj), D(Bj)) for Bj in levels])
    assert R*D(P) >= n+m2
    if anchor is None:
        return
    lam, mu = anchor
    for b, Ab in fibers.items():
        assert add(cmul(lam, b), mu) in Ab
    candidates = [{add(a, scale(M, bstar)) for a in Astar}]
    for Bj in levels:
        Qj = {add(add(cmul(lam, b), mu), scale(M, b)) for b in Bj}
        assert Qj <= P
        assert D(Qj) == D(Bj)
        candidates.append(Qj)
    if m1*2 <= n and len(fibers)*2 <= n:
        Q = max(candidates, key=lambda q: Fraction(len(q), D(q)))
        assert 2 <= len(Q) <= n//2
        assert Fraction(len(Q), D(Q)) > Fraction(n, D(P))
    else:
        assert n < 4*D(P)  # Gives C=12 with an arbitrary pair.


# The layer-cake inequality does not itself require a transversal.
check_layer_cake(fibers)
for _ in range(20):
    fine = list(product(range(-2, 3), repeat=2))
    coarse = rng.sample(list(product(range(4), repeat=2)), rng.randrange(2, 8))
    fs = {b: set(rng.sample(fine, rng.randrange(2, 9))) for b in coarse}
    check_layer_cake(fs)

# Balanced, common-anchor, and affine-anchor extraction cases.
coarse = list(product(range(3), repeat=2))
offsets = list(product(range(-2, 3), repeat=2))
offsets.remove((0, 0))
for lam, mu in [((0, 0), (0, 0)), ((1, 1), (2, -1))]:
    for _ in range(20):
        fs = {}
        for b in coarse:
            c = add(cmul(lam, b), mu)
            off = [(0, 0)]+rng.sample(offsets, rng.randrange(1, 8))
            fs[b] = {add(c, u) for u in off}
        check_layer_cake(fs, (lam, mu))
    # One heavy fine fiber.
    fs = {b: {add(cmul(lam, b), mu)} for b in coarse[:3]}
    b0 = coarse[0]
    c0 = add(cmul(lam, b0), mu)
    fs[b0] = {add(c0, u) for u in [(0, 0)]+offsets}
    check_layer_cake(fs, (lam, mu))
    # More than n/2 coarse sites.
    fs = {b: {add(cmul(lam, b), mu)} for b in coarse}
    c0 = add(cmul(lam, coarse[0]), mu)
    fs[coarse[0]].add(add(c0, (1, 2)))
    check_layer_cake(fs, (lam, mu))
print('Layer-cake, balanced C=0, and unbalanced C=12 checks passed.')

# Overlapping digit grids: keep the physical projection injective, but not
# evaluation on the distinct distance polynomials.
for s in (2, 4, 8, 16, 32, 64):
    fine_diffs = product(range(-(s-1), s), repeat=2)
    coarse_diffs = list(product(range(-1, 2), repeat=2))
    T = {(norm2(u), 2*dot(u, v), norm2(v))
         for u in fine_diffs for v in coarse_diffs
         if u != (0, 0) or v != (0, 0)}
    witness = {(x*x+y*y, 2*x, 1)
               for x in range(-(s-1), s) for y in range(s)}
    assert witness <= T
    assert len(witness) == (2*s-1)*s
    values = {evaluate(f, s) for f in T}
    grid_values = {x*x+y*y for x in range(2*s) for y in range(2*s)
                   if x or y}
    assert values == grid_values
    assert 0 not in values
    assert len(T) > len(values)
    print('Overlap:', 's=', s, 'n=', 4*s*s,
          'Dpoly=', len(T), 'Dactual=', len(values),
          'average evaluation multiplicity=', Fraction(len(T), len(values)))

print('All exact checks passed. No unrestricted contraction claim is made.')
