#!/usr/bin/env python3
"""Exact finite tests of WR. This script does NOT prove or disprove universal WR.

Coordinates are integers in a basis with positive-definite integral Gram matrix
[[aa,bb],[bb,cc]]. (2,1,2) represents a similarity of the triangular lattice.
No floating-point equality decisions are used. The displayed ratios are rounded.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product
from math import gcd, isqrt
from random import Random
import argparse


def line_key(A, B, C):
    """Primitive signed integer equation A*x+B*y=C."""
    assert A or B
    g = gcd(gcd(A, B), C)
    if A < 0 or (A == 0 and B < 0):
        g = -g
    return A // g, B // g, C // g


def setup(P, G):
    P = list(dict.fromkeys(P))
    aa, bb, cc = G
    assert len(P) >= 2 and aa > 0 and aa * cc > bb * bb
    def norm(x, y):
        return aa*x*x + 2*bb*x*y + cc*y*y
    return P, norm


def pair_method(P, G=(1, 0, 1)):
    """Compute w from endpoint pairs and m from independent collinear pairs."""
    P, norm = setup(P, G)
    n = len(P)
    aa, bb, cc = G
    norms = [norm(*p) for p in P]
    pins = [Counter() for _ in P]
    ws, line_pairs = Counter(), Counter()
    for i, j in combinations(range(n), 2):
        x, y = P[i]; X, Y = P[j]
        dx, dy = X-x, Y-y
        s = norm(dx, dy)
        pins[i][s] += 1; pins[j][s] += 1
        axis = line_key(2*(aa*dx+bb*dy), 2*(bb*dx+cc*dy),
                        norms[j]-norms[i])
        ws[axis] += 2
        line_pairs[line_key(dy, -dx, dy*x-dx*y)] += 1
    palette = set().union(*(set(c) for c in pins))
    D = len(palette)
    dp_sum = sum(map(len, pins))
    B = Fraction(n*(n-1)-dp_sum, D)
    R = 0
    for axis, t in line_pairs.items():
        m = (1 + isqrt(1+8*t)) // 2
        assert m*(m-1)//2 == t
        w = ws.get(axis, 0)
        assert w <= n-m
        R += m * min(w, m*(m-1))
    I = sum(k*(k-1) for pin in pins for k in pin.values())
    return dict(n=n, D=D, dp_sum=dp_sum, B=B, R=R, I=I,
                ratio=B*B/(n*n+R))


def center_method(P, G=(1, 0, 1), weighted=False, reflect_check=False):
    """Independent method: enumerate full pinned fibers and their actual centers.

    For each center and axis, all reflected pairs occur among its isosceles
    witnesses. Hence their count is w/2, independent of the chosen center.
    Counting the centers of an axis gives m directly, not via collinear pairs.
    """
    P, norm = setup(P, G)
    n = len(P)
    aa, bb, cc = G
    norms = [norm(*p) for p in P]
    palette = set()
    dp_sum = I = 0
    axes = {}  # axis -> [number of actual centers, ordered reflected pair count]
    mass = defaultdict(Fraction)
    for p, (px, py) in enumerate(P):
        fibers = defaultdict(list)
        for j, (x, y) in enumerate(P):
            if j != p:
                fibers[norm(x-px, y-py)].append(j)
        palette.update(fibers)
        dp_sum += len(fibers)
        local = Counter()
        for fiber in fibers.values():
            k = len(fiber)
            I += k*(k-1)
            for a, b in combinations(fiber, 2):
                dx, dy = P[b][0]-P[a][0], P[b][1]-P[a][1]
                axis = line_key(2*(aa*dx+bb*dy), 2*(bb*dx+cc*dy),
                                norms[b]-norms[a])
                assert axis[0]*px + axis[1]*py == axis[2]
                local[axis] += 2
                if weighted:
                    mass[axis] += Fraction(2, k)  # global division by D below
        for axis, w in local.items():
            if axis in axes:
                assert axes[axis][1] == w
                axes[axis][0] += 1
            else:
                axes[axis] = [1, w]
    D = len(palette)
    B = Fraction(n*(n-1)-dp_sum, D)
    R = sum(m*min(w, m*(m-1)) for m, w in axes.values() if m >= 2)
    assert I == sum(m*w for m, w in axes.values())
    if reflect_check:
        point_set = set(P)
        for (A, BB, C), (m, w) in axes.items():
            U, V = cc*A-bb*BB, aa*BB-bb*A
            denominator = A*U + BB*V
            m_check = w_check = 0
            for x, y in P:
                t = A*x + BB*y - C
                if not t:
                    m_check += 1
                    continue
                X = x*denominator - 2*t*U
                Y = y*denominator - 2*t*V
                if X % denominator == 0 and Y % denominator == 0:
                    w_check += (X//denominator, Y//denominator) in point_set
            assert (m, w) == (m_check, w_check)
    if weighted:
        assert sum(mass.values(), Fraction()) / D == B
        for M in (1, 2, 4):
            low = sum((mass[a] for a, (m, _) in axes.items() if m <= M),
                      Fraction()) / D
            high = B-low
            assert low*low <= Fraction(M*n*n*(n-1), D)
            assert low*low <= M*n*(B+n)
            assert B <= 2*high + (M+1)*n
    return dict(n=n, D=D, dp_sum=dp_sum, B=B, R=R, I=I,
                ratio=B*B/(n*n+R))


def disk(L, triangular=False):
    return [(x, y) for x, y in product(range(-2*L, 2*L+1), repeat=2)
            if x*x + (x*y if triangular else 0) + y*y <= L*L]


def show(name, P, G=(1, 0, 1), independent=False):
    result = pair_method(P, G)
    if independent:
        assert result == center_method(P, G, weighted=len(P) <= 100,
                                        reflect_check=len(P) <= 100)
    display = dict(result)
    display['B'] = str(display['B'])
    display['ratio'] = float(display['ratio'])
    print(name, display, flush=True)
    return result


def verify():
    grid = list(product(range(3), repeat=2))
    checked = 0
    for G in ((1, 0, 1), (2, 1, 2), (1, 0, 5)):
        for mask in range(1 << len(grid)):
            P = [p for i, p in enumerate(grid) if mask >> i & 1]
            if len(P) < 2:
                continue
            a = pair_method(P, G)
            b = center_method(P, G, weighted=True, reflect_check=True)
            assert a == b
            checked += 1
    print('Exhaustive method/weight/reflection checks:', checked, flush=True)
    for L in (4, 8, 12, 16, 20):
        show('square disk '+str(L), disk(L), independent=True)
        result = show('triangular disk '+str(L), disk(L, True), (2, 1, 2),
                      independent=True)
        if L == 4:
            assert result['n'] == 61 and result['D'] == 23
            assert result['dp_sum'] == 1106 and result['R'] == 8568
            assert result['ratio'] == Fraction(6522916, 6500881) > 1
        if L == 20:
            assert result['n'] == 1459 and result['D'] == 422
            assert result['dp_sum'] == 441002 and result['R'] == 9044940
    print('All exact cross-checks passed. Universal WR and CW remain unresolved.',
          flush=True)


def families():
    rng = Random(123456)
    for L in (4, 8, 16, 24, 32):
        grid = list(product(range(L), repeat=2))
        show('grid '+str(L), grid)
        for delta in (.75, .5, .25):
            show('random '+str((L, delta)), [p for p in grid if rng.random() < delta])
        show('triangular parallelogram '+str(L), grid, (2, 1, 2))
        for q in (2, 3, 5, 10, 101):
            show('rectangular '+str((L, q)), grid, (1, 0, q))
        show('three parity classes '+str(L),
             [p for p in grid if p[0] % 2 == 0 or p[1] % 2 == 0])
        show('annulus '+str(L), [(x, y) for x, y in product(range(-L, L+1), repeat=2)
                                if L*L//2 <= x*x+y*y <= L*L])
    for q in (3, 5, 7, 11):
        grid = list(product(range(24), repeat=2))
        show('periodic parabola '+str(q), [(x,y) for x,y in grid if (y-x*x)%q == 0])
        show('periodic circle '+str(q), [(x,y) for x,y in grid if (x*x+y*y-1)%q == 0])
        show('periodic circle complement '+str(q),
             [(x,y) for x,y in grid if (x*x+y*y-1)%q != 0])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--families', action='store_true')
    args = parser.parse_args()
    verify()
    if args.families:
        families()
