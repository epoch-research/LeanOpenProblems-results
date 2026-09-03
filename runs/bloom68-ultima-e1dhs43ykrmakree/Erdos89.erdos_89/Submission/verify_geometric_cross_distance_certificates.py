#!/usr/bin/env python3
"""Exact checks for geometric_cross_distance_certificates.md.

No disk-defect search is claimed. All distance equality, circumcenter, and
lens membership tests below use integers or fractions. Irrational distances
are represented by exact coefficients in specified real number fields.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, ceil
import random

Point = tuple[int | F, int | F]


def binom3(k: int) -> int:
    return comb(k, 3) if k >= 3 else 0


def balanced_bin(m: int, d: int) -> int:
    q, u = divmod(m, d)
    return (d-u)*binom3(q) + u*binom3(q+1)


def compositions(m: int, d: int):
    if d == 1:
        yield (m,)
    else:
        for k in range(m+1):
            for rest in compositions(m-k, d-1):
                yield (k,) + rest


def sqdist(a: Point, b: Point):
    return (a[0]-b[0])**2 + (a[1]-b[1])**2


def circumcenter(a: Point, b: Point, z: Point):
    ux, uy = b[0]-a[0], b[1]-a[1]
    vx, vy = z[0]-a[0], z[1]-a[1]
    det = ux*vy-uy*vx
    if det == 0:
        return None
    ub = F(b[0]**2+b[1]**2-a[0]**2-a[1]**2, 2)
    vz = F(z[0]**2+z[1]**2-a[0]**2-a[1]**2, 2)
    return (F(ub*vy-vz*uy, det), F(ux*vz-vx*ub, det))


def lens_over_edge(a: Point, b: Point, z: Point, h: int | F) -> bool:
    """Exact (1.1), with a,b required to be the unique longest edge."""
    vx, vy = b[0]-a[0], b[1]-a[1]
    wx, wy = z[0]-a[0], z[1]-a[1]
    l2 = vx*vx+vy*vy
    if not (sqdist(a, z) < l2 and sqdist(b, z) < l2):
        return False
    dot, cross = wx*vx+wy*vy, vx*wy-vy*wx
    if cross == 0 or not 0 < dot < l2:
        return False
    # 2h sqrt(l2) |cross| <= dot(l2-dot); both sides are nonnegative.
    return 4*h*h*l2*cross*cross <= dot*dot*(l2-dot)*(l2-dot)


def lens_triangle(a: Point, b: Point, z: Point, h: int | F) -> bool:
    ds = (sqdist(a, b), sqdist(a, z), sqdist(b, z))
    largest = max(ds)
    if ds.count(largest) != 1:
        return False
    j = ds.index(largest)
    if j == 0:
        return lens_over_edge(a, b, z, h)
    if j == 1:
        return lens_over_edge(a, z, b, h)
    return lens_over_edge(b, z, a, h)


def check_balanced_bins():
    tests = 0
    for m in range(15):
        for d in range(1, 6):
            vals = [sum(binom3(k) for k in ks) for ks in compositions(m, d)]
            assert min(vals) == balanced_bin(m, d)
            if m > 2*d:
                assert balanced_bin(m, d) >= F(m*(m-d)*(m-2*d), 6*d*d)
            tests += 1
    print(f'Balanced-bin exact minima and Jensen bounds: PASS ({tests} parameter pairs)')


def check_cross_instance(name: str, A: list[Point], B: list[Point],
                         c: Point, r: int | F, R: int | F):
    assert R > r >= 0
    assert len(A) == len(set(A)) and len(B) == len(set(B))
    assert all(sqdist(a, c) <= r*r for a in A)
    assert all(sqdist(p, c) >= R*R for p in B)
    m, s = len(A), len(B)
    rows = [Counter(sqdist(a, p) for a in A) for p in B]
    d = len(set().union(*(set(row) for row in rows)))
    cc_count = sum(sum(binom3(k) for k in row.values()) for row in rows)
    per_row_lower = sum(balanced_bin(m, len(row)) for row in rows)
    Bset = set(B)
    T, far_T, lens = 0, 0, 0
    for a, b, z in combinations(A, 3):
        p = circumcenter(a, b, z)
        inside_lens = lens_triangle(a, b, z, R-r)
        lens += inside_lens
        if p in Bset:
            T += 1
            assert inside_lens
        if p is not None and sqdist(p, c) >= R*R:
            far_T += 1
            assert inside_lens
    assert cc_count == T
    assert s*balanced_bin(m, d) <= per_row_lower <= T <= lens
    if m > 2*d:
        assert F(s*m*(m-d)*(m-2*d), 6*d*d) <= lens
    if d <= F(m, 4):
        assert lens > 0
        assert d*d >= F(s*m*m*m, 16*lens)
    for row in rows:
        witness_count = sum(k//3 for k in row.values())
        promised = max(0, ceil(F(m-2*len(row), 3)))
        assert witness_count >= promised
    print(f'  {name}: m={m}, s={s}, d={d}, sF={s*balanced_bin(m,d)}, '
          f'T_B={T}, T_far={far_T}, lens={lens}')
    return m, s, d, T, lens


def check_cross_geometry():
    print('Cross-support / unique-circumcenter / lens inequalities:')
    arc = [(65, 0), (63, 16), (63, -16), (56, 33), (56, -33)]
    result = check_cross_instance('Pythagorean arc equality', arc, [(0, 0)],
                                 (65, 0), 35, 65)
    assert result == (5, 1, 1, 10, 10)
    near_arc = arc + [(F(65)+F(1, 10**40), 0)]
    check_cross_instance('two cross radii separated by 10^(-40)', near_arc, [(0, 0)],
                         (65, 0), 35, 65)
    symmetric = [(x, y) for x in range(-3, 4)
                 for y in (-3, -2, -1, 1, 2, 3)]
    check_cross_instance('two exterior centers, nonzero lower bound', symmetric,
                         [(-5, 0), (5, 0)], (0, 0), F(9, 2), 5)
    tall = [(x, y) for x in range(-2, 3)
            for y in list(range(-8, 0))+list(range(1, 9))]
    check_cross_instance('tall rectangle, two exterior centers', tall,
                         [(-9, 0), (9, 0)], (0, 0), F(17, 2), 9)
    grid = list(product(range(-3, 4), repeat=2))
    check_cross_instance('integer grid, four exterior centers', grid,
                         [(-8, 0), (8, 0), (0, -8), (0, 8)], (0, 0), 5, 8)
    rng = random.Random(49173)
    ambient = list(product(range(-4, 5), repeat=2))
    for trial in range(8):
        A = rng.sample(ambient, 14)
        B = rng.sample([(x, y) for x in range(-14, 15) for y in range(-14, 15)
                        if x*x+y*y >= 100], 7)
        check_cross_instance(f'rational random {trial+1}', A, B, (0, 0), 6, 10)
    print('  PASS: all comparisons exact, with no distance tolerances')


def check_field_core():
    A = list(product(range(-6, 7), repeat=2))
    m = len(A)
    for epsilon in (F(1, 10), F(1, 10**10), F(1, 10**40)):
        # p=(epsilon sqrt(2),0); coefficient tuple in Q(sqrt(2)).
        row2 = Counter((F(x*x+y*y)+2*epsilon**2, -2*epsilon*x) for x, y in A)
        assert max(row2.values()) <= 2
        assert len(row2) >= ceil(F(m, 2))
        # p=(epsilon sqrt(2),epsilon sqrt(3)); 1,sqrt(2),sqrt(3) are independent.
        row23 = Counter((F(x*x+y*y)+5*epsilon**2, -2*epsilon*x, -2*epsilon*y)
                        for x, y in A)
        assert max(row23.values()) == 1 and len(row23) == m
    # Being outside the core is essential: a rational center can have a large fiber.
    rational_row = Counter(x*x+y*y for x, y in A if (x, y) != (0, 0))
    assert max(rational_row.values()) >= 12
    # Core in Q(sqrt(2))^2, outlier (epsilon sqrt(3),0), using the basis
    # 1,sqrt(2),sqrt(3),sqrt(6) of the degree-four real field.
    epsilon = F(1, 10**40)
    extended_core = list(product(range(-2, 3), repeat=4))
    extended_row = Counter((F(a*a+2*b*b+c*c+2*d*d)+3*epsilon**2,
                            F(2*(a*b+c*d)), -2*epsilon*a, -2*epsilon*b)
                           for a, b, c, d in extended_core)
    assert max(extended_row.values()) == 2
    assert len(extended_row) >= ceil(F(len(extended_core), 2))
    print(f'Proper field-core bound: PASS (Q-core m={m}, Q(sqrt(2))-core m='
          f'{len(extended_core)}; exact shifts down to 10^(-40))')


def grid_palette(L: int) -> set[int]:
    return {x*x+y*y for x in range(L) for y in range(L) if x or y}


# A point in Q(sqrt(2))^2 is ((x0,x1),(y0,y1)), representing x0+x1 sqrt(2), etc.
def quadratic_sq(x):
    a, b = x
    return (a*a+2*b*b, 2*a*b)


def quadratic_dist2(p, q):
    x = (p[0][0]-q[0][0], p[0][1]-q[0][1])
    y = (p[1][0]-q[1][0], p[1][1]-q[1][1])
    sx, sy = quadratic_sq(x), quadratic_sq(y)
    return sx[0]+sy[0], sx[1]+sy[1]


def check_perturbation():
    print('One-corner perturbation identity D(P)=D(G)+L^2-1:')
    for L in (2, 3, 4, 6, 9, 12):
        G = list(product(range(L), repeat=2))
        core = [p for p in G if p != (0, 0)]
        palette = grid_palette(L)
        assert {sqdist(a, b) for a, b in combinations(core, 2)} == palette
        for epsilon in (F(1, 10), F(1, 10**40)):
            points = [((F(x), F(0)), (F(y), F(0))) for x, y in core]
            points.append(((F(0), epsilon), (F(0), F(0))))
            actual = {quadratic_dist2(a, b) for a, b in combinations(points, 2)}
            assert len(actual) == len(palette)+L*L-1
        print(f'  L={L}: n={L*L}, D(G)={len(palette)}, D(P)={len(actual)} (all pairs)')
    for L in (20, 50, 100, 200):
        epsilon = F(1, 10**40)
        old = {(F(k), F(0)) for k in grid_palette(L)}
        new = {(F(x*x+y*y)+2*epsilon**2, -2*epsilon*x)
               for x, y in product(range(L), repeat=2) if x or y}
        assert len(new) == L*L-1 and old.isdisjoint(new)
        print(f'  L={L}: n={L*L}, D(G)={len(old)}, D(P)={len(old)+len(new)} '
              '(exact old/new support disjointness)')
    print('  PASS')


def box_points(center: tuple[F, F], N: int):
    delta = F(1, 200)
    lo = [ceil(N*(t-delta)) for t in center]
    hi = [(N*(t+delta)).numerator//(N*(t+delta)).denominator for t in center]
    return [(x, y) for x in range(lo[0], hi[0]+1) for y in range(lo[1], hi[1]+1)]


def check_lens_obstruction():
    # Three fixed 0.01-by-0.01 boxes around a strict lens configuration.
    # These rational bounds prove the lens condition for EVERY choice of one point per box.
    vxlo, vxhi, vyabs = F(79, 100), F(81, 100), F(1, 100)
    wxlo, wxhi, wylo, wyhi = F(39, 100), F(41, 100), F(4, 100), F(6, 100)
    l2lo, l2hi = vxlo**2, vxhi**2+vyabs**2
    crosslo = vxlo*wylo-vyabs*wxhi
    crosshi = vxhi*wyhi+vyabs*wxhi
    dotlo = vxlo*wxlo-vyabs*wyhi
    assert crosslo > 0 and dotlo > 0
    assert wxhi**2+wyhi**2 < l2lo  # both shorter sides obey this bound
    assert 4*l2hi*crosshi**2 < dotlo**4
    centers = ((F(1, 10), F(1, 5)), (F(9, 10), F(1, 5)), (F(1, 2), F(1, 4)))
    print('Growing-grid lens obstruction:')
    for N in (200, 400, 1000, 2000):
        boxes = [box_points(center, N) for center in centers]
        lower = len(boxes[0])*len(boxes[1])*len(boxes[2])
        assert len(set().union(*map(set, boxes))) == sum(map(len, boxes))
        if N <= 400:
            assert all(lens_over_edge(a, b, z, N) for a in boxes[0]
                       for b in boxes[1] for z in boxes[2])
        print(f'  N={N}, |A|={(N+1)**2}, box sizes={tuple(map(len,boxes))}, '
              f'certified lens triples >= {lower}')
    print('  PASS: fixed positive-volume boxes give Omega(N^6), not O(N^4 log^2 N)')

def check_cubic_cover_bound():
    for J in (1, 2, 7, 49, 289):
        for k in list(range(2001)) + [10000, 100001]:
            assert balanced_bin(k, J) >= F(k**3, 6*J*J)-F(k*k, 2)
    # Exact Euler-factor identity for the cubic representation moment.
    for k in range(40):
        coefficient = comb(k+3, 3)
        if k >= 1:
            coefficient += 4*comb(k+2, 3)
        if k >= 2:
            coefficient += comb(k+1, 3)
        assert coefficient == (k+1)**3
    h_coefficients = [0]*7
    for j, a in enumerate((1, 4, 1)):
        for k in range(5):
            h_coefficients[j+k] += a*((-1)**k)*comb(4, k)
    assert h_coefficients == [1, 0, -9, 16, -9, 0, 1]
    print('Finite cubic-bin bound and cubic-moment Euler factors: PASS')


def check_actual_center_cover():
    print('Finite disk-cover inequality with actual exterior centers:')
    for L in (8, 16, 24, 32, 48, 64, 128):
        step, r = L//8, L//8
        P0 = list(product(range(-L//2, L//2+1), repeat=2))
        anchors = P0 if L <= 48 else list(product(range(-4, 5), repeat=2))
        centers = list(product(range(-L, L+1, step), repeat=2))
        assert len(centers) == 289
        n = (2*L+1)**2
        local_offsets = [(x, y) for x in range(-r, r+1) for y in range(-r, r+1)
                         if x*x+y*y <= r*r]
        for c in centers:
            m = sum(-L <= c[0]+x <= L and -L <= c[1]+y <= L
                    for x, y in local_offsets)
            assert 3 <= m <= n//2 and m >= (L//16+1)**2
            b = sum(sqdist(p, c) >= 4*r*r for p in P0)
            assert b >= F(3*L*L, 4)
        vectors = [(x, y, x*x+y*y)
                   for x in range(-L//2, L//2+1)
                   for y in range(-L//2, L//2+1)
                   if (3*L//8)**2 <= x*x+y*y <= (L//2)**2]
        r2 = Counter(t for x, y, t in vectors)
        lower_per_center = sum(balanced_bin(k, 289) for k in r2.values())
        witnesses = set()
        assigned_total = 0
        for p in anchors:
            cells = {}
            for vx, vy, t in vectors:
                q = (p[0]+vx, p[1]+vy)
                assert -L <= q[0] <= L and -L <= q[1] <= L
                indices = []
                for coordinate in q:
                    k, rem = divmod(coordinate+L, step)
                    if 2*rem > step:
                        k += 1
                    indices.append(k)
                c = (-L+indices[0]*step, -L+indices[1]*step)
                assert sqdist(q, c) <= r*r
                assert sqdist(p, c) >= 4*r*r
                cells.setdefault((t, c), []).append(q)
            row_count = sum(binom3(len(points)) for points in cells.values())
            assert row_count >= lower_per_center
            assigned_total += row_count
            for (t, c), points in cells.items():
                for triple in combinations(points, 3):
                    key = tuple(sorted(triple))
                    assert key not in witnesses
                    witnesses.add(key)
                    assert circumcenter(*triple) == p
                    assert lens_triangle(*triple, r)
        assert len(witnesses) == assigned_total
        assert assigned_total >= len(anchors)*lower_per_center
        if L >= 64:
            assert assigned_total > 0
        print(f'  L={L}: n={n}, |P0|={len(P0)}, tested centers={len(anchors)}, '
              f'assigned actual-center triples={assigned_total}, '
              f'balanced-bin RHS={len(anchors)*lower_per_center}')
    print('  PASS: all selected disks admissible; every witness has its actual exterior center')
    print('  The asymptotic cubic-log growth uses the proved moment asymptotic, not these small cases.')



def main():
    check_balanced_bins()
    check_cross_geometry()
    check_field_core()
    check_perturbation()
    check_lens_obstruction()
    check_cubic_cover_bound()
    check_actual_center_cover()
    print('ALL EXACT FINITE CHECKS PASSED')


if __name__ == '__main__':
    main()
