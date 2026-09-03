#!/usr/bin/env python3
"""Exact finite checks for disk_capacity_localization.md.

Requires NumPy.  Distances and disk membership are integer-exact.  The large
point-set distance calculation uses integer polynomial multiplication, not FFT.
No finite search here is asserted to enumerate all closed-disk intersections.
The selected disks give *upper bounds* for the disk defect, not counterexamples.
"""
from __future__ import annotations

import argparse
import math
import random
from fractions import Fraction
from itertools import product

import numpy as np


PARITIES = list(product(range(2), repeat=2))


def sums_two_squares(limit: int) -> tuple[np.ndarray, np.ndarray]:
    flag = np.zeros(limit + 1, dtype=np.bool_)
    squares = np.arange(math.isqrt(limit) + 1, dtype=np.int64) ** 2
    for a2 in squares:
        end = math.isqrt(limit - int(a2))
        flag[int(a2) + squares[: end + 1]] = True
    flag[0] = False
    return flag, np.cumsum(flag, dtype=np.int64)


def exact_autocorrelation(mask: np.ndarray) -> np.ndarray:
    """Count all ordered displacement pairs by carry-free bigint multiplication.

    If the input has nx columns, use row stride 2*nx-1.  Thus x-coordinate
    sums never wrap into another row.  Digits have base > number of points,
    so convolution coefficients never carry into neighboring digits either.
    """
    mask = np.asarray(mask, dtype=np.bool_)
    ny, nx = mask.shape
    n = int(mask.sum())
    if n < (1 << 16):
        dtype = np.dtype('<u2')
    elif n < (1 << 32):
        dtype = np.dtype('<u4')
    else:
        raise ValueError('This verification routine is intended for n < 2^32')
    stride = 2 * nx - 1
    length = (ny - 1) * stride + nx
    aa = np.zeros(length, dtype=dtype)
    bb = np.zeros(length, dtype=dtype)
    for y in range(ny):
        aa[y * stride:y * stride + nx] = mask[y]
        bb[y * stride:y * stride + nx] = mask[ny - 1 - y, ::-1]
    a = int.from_bytes(aa.tobytes(), 'little')
    b = int.from_bytes(bb.tobytes(), 'little')
    out_length = (2 * ny - 1) * stride
    raw = (a * b).to_bytes(out_length * dtype.itemsize, 'little')
    corr = np.frombuffer(raw, dtype=dtype).reshape(2 * ny - 1, stride)
    assert int(corr[ny - 1, nx - 1]) == n
    assert int(corr.sum(dtype=np.uint64)) == n * n
    assert np.array_equal(corr, corr[::-1, ::-1])
    return corr


def support_from_correlation(corr: np.ndarray) -> set[int]:
    hy, hx = corr.shape[0] // 2, corr.shape[1] // 2
    yy, xx = np.nonzero(corr)
    values = (yy.astype(np.int64) - hy) ** 2 + (xx.astype(np.int64) - hx) ** 2
    out = set(map(int, np.unique(values)))
    out.discard(0)
    return out


def exact_support(mask: np.ndarray) -> set[int]:
    return support_from_correlation(exact_autocorrelation(mask))


def brute_support(points: list[tuple[int, int]]) -> set[int]:
    return {(x - u) ** 2 + (y - v) ** 2
            for i, (x, y) in enumerate(points) for u, v in points[:i]}


def check_analytic_constants() -> None:
    lam = Fraction(1, 1024)
    q = Fraction(1, 2)
    strip_bound = 4 * lam + 8 * lam / (q - lam) + 8 * lam**2 / (q*q - lam**2)
    assert strip_bound < Fraction(1, 4)
    balanced_bound = Fraction(22, 7) * (Fraction(1, 200) + Fraction(5, 14))**2
    assert balanced_bound < Fraction(1, 2)
    # With the bad-strip fraction <= 1/4 and pi>3, residual contraction <=7/16.
    assert Fraction(7, 16) < Fraction(1, 2)
    # alpha = 1/10 and 3+alpha/4=121/40.
    assert Fraction(3) + Fraction(1, 10) / 4 == Fraction(121, 40)
    print('Rational packing checks: PASS')
    print(f'  boundary-strip bracket < {float(strip_bound):.9f} < 1/4')
    print(f'  balanced-cardinality factor < {float(balanced_bound):.9f} < 1/2')


def check_exact_convolution() -> None:
    rng = np.random.default_rng(20261102)
    count = 0
    for ny in range(1, 9):
        for nx in range(1, 9):
            mask = rng.random((ny, nx)) < .6
            corr = exact_autocorrelation(mask)
            pts = [(int(x), int(y)) for y, x in np.argwhere(mask)]
            direct = np.zeros(corr.shape, dtype=np.int64)
            for x, y in pts:
                for u, v in pts:
                    direct[y - v + ny - 1, x - u + nx - 1] += 1
            assert np.array_equal(corr, direct)
            assert support_from_correlation(corr) == brute_support(pts)
            count += 1
    # Exercise the wider-digit branch with n > 2^16. A one-row interval has
    # the exact triangular autocorrelation, so no quadratic reference work.
    size = (1 << 16) + 3
    corr = exact_autocorrelation(np.ones((1, size), dtype=np.bool_))
    expected = np.concatenate((np.arange(1, size), np.arange(size, 0, -1)))
    assert np.array_equal(corr[0], expected)
    print(f'Carry-free integer autocorrelation: PASS ({count} small arrays + 32-bit-digit branch)')


def check_parity_endpoints() -> None:
    centers = [(Fraction(0), Fraction(0)),
               (Fraction(1, 3), Fraction(-2, 5))]
    count = 0
    for missing in PARITIES:
        for vx in range(-24, 25):
            for vy in range(-24, 25):
                if vx == vy == 0:
                    continue
                allowed = [u for u in PARITIES
                           if u != missing and ((u[0] + vx) % 2, (u[1] + vy) % 2) != missing]
                assert len(allowed) >= 2
                u = allowed[0]
                for cx, cy in centers:
                    target = (cx - Fraction(vx, 2), cy - Fraction(vy, 2))
                    p = tuple(u[i] + 2 * round((target[i] - u[i]) / 2) for i in range(2))
                    err2 = sum((Fraction(p[i]) - target[i])**2 for i in range(2))
                    assert err2 <= 2
                    assert (p[0] % 2, p[1] % 2) != missing
                    assert ((p[0] + vx) % 2, (p[1] + vy) % 2) != missing
                    count += 1
    print(f'Parity endpoint realization: PASS ({count:,} exact rational cases)')


def parity_inner_threshold(R: int) -> int:
    assert R >= 2
    # floor((2R-2sqrt(2))^2) = 4R^2+8-ceil(sqrt(128R^2)).
    sq = 128 * R * R
    root = math.isqrt(sq)
    assert root * root != sq
    return 4 * R * R + 7 - root


def disk_mask(R: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    coords = np.arange(-R, R + 1, dtype=np.int64)
    yy, xx = np.meshgrid(coords, coords, indexing='ij')
    return xx, yy, xx*xx + yy*yy <= R*R


def check_parity_distance_support(norm_flag: np.ndarray) -> None:
    count = 0
    for R in range(2, 13):
        xx, yy, full = disk_mask(R)
        inner = parity_inner_threshold(R)
        required = set(map(int, np.flatnonzero(norm_flag[:inner + 1])))
        for bx, by in PARITIES:
            base = full & ~((xx % 2 == bx) & (yy % 2 == by))
            supp = exact_support(base)
            assert required <= supp
            assert max(supp) <= 4*R*R
            count += 1
    print(f'Three-parity-class support containment: PASS ({count} whole finite supports)')


def check_closest_pair() -> None:
    rng = random.Random(77)
    for _ in range(100):
        pts = rng.sample(list(product(range(-6, 7), repeat=2)), 15)
        d, p, q = min(((p[0]-q[0])**2 + (p[1]-q[1])**2, p, q)
                      for i, p in enumerate(pts) for q in pts[:i])
        selected = [x for x in pts
                    if (2*x[0]-p[0]-q[0])**2 + (2*x[1]-p[1]-q[1])**2 <= d]
        assert len(selected) == 2
    print('Closed closest-pair disks: PASS (100 configurations)')


def check_matching_gadget() -> None:
    rng = random.Random(1283)
    vectors_checked = 0
    matchings_checked = 0
    for R in (12, 16, 24):
        xx, yy, full = disk_mask(R)
        corr = exact_autocorrelation(full)
        hy, hx = corr.shape[0]//2, corr.shape[1]//2
        dy, dx = np.meshgrid(np.arange(-hy, hy+1), np.arange(-hx, hx+1), indexing='ij')
        relevant = (dx*dx + dy*dy > 0) & (dx*dx + dy*dy <= (2*R-10)**2)
        edge_counts = corr[relevant].astype(np.uint64)
        assert np.all(edge_counts * edge_counts >= 16*R)
        vectors_checked += int(relevant.sum())
        vecs = [(int(x), int(y)) for y, x in zip(dy[relevant], dx[relevant])]
        pts = {(int(x), int(y)) for y, x in np.argwhere(full)}
        for vx, vy in rng.sample(vecs, min(40, len(vecs))):
            edges = [(p, (p[0]+vx, p[1]+vy)) for p in pts
                     if (p[0]+vx, p[1]+vy) in pts]
            used = set()
            matching = []
            for p, q in edges:
                if p not in used and q not in used:
                    used.add(p)
                    used.add(q)
                    matching.append((p, q))
            assert 3 * len(matching) >= len(edges)
            assert len(used) == 2 * len(matching)
            matchings_checked += 1
    print(f'Random-sampling support gadget: PASS ({vectors_checked:,} vector counts, '
          f'{matchings_checked} vertex-disjoint matchings)')


class CircleCounter:
    def __init__(self, mask: np.ndarray, R: int):
        self.mask = mask
        self.R = R
        self.prefix = np.pad(np.cumsum(mask, axis=1, dtype=np.int64), ((0, 0), (1, 0)))
        self.cross_sections: dict[int, np.ndarray] = {}

    def count(self, cx: int, cy: int, r: int) -> int:
        if r not in self.cross_sections:
            self.cross_sections[r] = np.array([math.isqrt(r*r - y*y)
                                               for y in range(-r, r+1)], dtype=np.int64)
        ys = np.arange(max(-self.R, cy-r), min(self.R, cy+r)+1, dtype=np.int64)
        if len(ys) == 0:
            return 0
        half_width = self.cross_sections[r][ys-cy+r]
        left = np.maximum(-self.R, cx-half_width)
        right = np.minimum(self.R, cx+half_width)
        valid = left <= right
        ys, left, right = ys[valid], left[valid], right[valid]
        return int((self.prefix[ys+self.R, right+self.R+1]
                    - self.prefix[ys+self.R, left+self.R]).sum())


def finite_cut_certificate(mask: np.ndarray, R: int, S: np.ndarray) -> tuple:
    n = int(mask.sum())
    counter = CircleCounter(mask, R)
    # Start with the exact closest-pair lower bound K=2.
    best_q, best_cap = 2, 1
    best_disk = None
    radii = sorted(set([1, 2, 3, 4, 5, 6] + [max(1, round(R*k/32)) for k in range(1, 33)]))
    step = max(1, R//8)
    coords = sorted(set(range(-R, R+1, step)) | {0, -R, R})
    tested = 0
    for r in radii:
        cap = int(S[4*r*r])
        centers = set(product(coords, repeat=2))
        # Additional off-center candidates tangent to the outer disk.
        for s in (R-r, max(0, R-r-1), R//2, 3*R//4):
            centers.update([(s, 0), (-s, 0), (0, s), (0, -s)])
        for cx, cy in centers:
            q = counter.count(cx, cy, r)
            tested += 1
            if 2 <= q <= n//2 and q*best_cap > best_q*cap:
                best_q, best_cap = q, cap
                best_disk = (cx, cy, r)
    if best_disk is None:
        return Fraction(4), 'closest pair', tested
    xx, yy, _ = disk_mask(R)
    cx, cy, r = best_disk
    cut = mask & ((xx-cx)**2 + (yy-cy)**2 <= r*r)
    assert int(cut.sum()) == best_q
    assert 2 <= best_q <= n//2
    ys, xs = np.nonzero(cut)
    cropped = cut[ys.min():ys.max()+1, xs.min():xs.max()+1]
    actual_D = len(exact_support(cropped))
    assert 1 <= actual_D <= best_cap
    lower_phi = Fraction(best_q*best_q, actual_D*actual_D)
    desc = f'center=({cx},{cy}), r={r}, q={best_q}, D(Q)={actual_D}'
    return lower_phi, desc, tested


def check_off_center_restorations(S: np.ndarray, quick: bool) -> None:
    rng = np.random.default_rng(340159)
    radii = (16, 32) if quick else (16, 32, 64, 128)
    max_upper_defect = None
    total_candidates = 0
    print('Finite restoration tests (actual D(P), actual D(Q); candidates need not exhaust all disks):')
    for R in radii:
        xx, yy, full = disk_mask(R)
        fourth = full & (xx % 2 == 1) & (yy % 2 == 1)
        base = full & ~fourth
        scale = max(1, R//7)
        patterns = {
            'base': base,
            'full': full,
            'outer-width-1': base | (fourth & (xx*xx+yy*yy >= (R-1)**2)),
            'outer-width-R/4': base | (fourth & (xx*xx+yy*yy >= (R-R//4)**2)),
            'irregular-blocks': base | (fourth & (((xx//scale + 2*(yy//scale)) % 3 == 0)
                                                | ((xx*xx+yy*yy) % 19 < 4))),
            'random-37pct': base | (fourth & (rng.random(full.shape) < .37)),
        }
        for name, mask in patterns.items():
            n = int(mask.sum())
            supp = exact_support(mask)
            D = len(supp)
            assert int(S[parity_inner_threshold(R)]) <= D <= int(S[4*R*R])
            phi = Fraction(n*n, D*D)
            cut_phi, desc, tested = finite_cut_certificate(mask, R, S)
            total_candidates += tested
            upper_defect = phi - cut_phi
            if max_upper_defect is None or upper_defect > max_upper_defect:
                max_upper_defect = upper_defect
            print(f'  R={R:3} {name:18} n={n:6} D={D:5} '
                  f'Phi={float(phi):8.4f}  certified defect <= {float(upper_defect):8.4f}')
            print(f'      {desc}')
    print(f'  Tested {total_candidates:,} integer-center/radius candidates, plus closest pairs.')
    print(f'  Largest certified upper defect in this finite list: {float(max_upper_defect):.6f}')


def check_sparse_samples(S: np.ndarray, quick: bool) -> None:
    rng = np.random.default_rng(18829)
    radii = (24,) if quick else (24, 48, 96)
    print('Sparse sample checks (one reproducible sample per radius; not an asymptotic proof):')
    for R in radii:
        _, _, full = disk_mask(R)
        L = math.log(4*R*R)
        theta = L**(-.25)
        mask = full & (rng.random(full.shape) < theta)
        corr = exact_autocorrelation(mask)
        hy, hx = corr.shape[0]//2, corr.shape[1]//2
        dy, dx = np.meshgrid(np.arange(-hy, hy+1), np.arange(-hx, hx+1), indexing='ij')
        required = (dx*dx+dy*dy > 0) & (dx*dx+dy*dy <= (2*R-10)**2)
        missing = int(np.count_nonzero(required & (corr == 0)))
        n = int(mask.sum())
        D = len(support_from_correlation(corr))
        phi = Fraction(n*n, D*D)
        cut_phi, desc, _ = finite_cut_certificate(mask, R, S)
        print(f'  R={R:3} theta={theta:.6f} n={n:6} D={D:5} '
              f'missing required vectors={missing}; certified defect <= {float(phi-cut_phi):.6f}')
        print(f'      {desc}')
        # For these fixed seeds the actual full inner support is checked, not assumed.
        assert missing == 0
        assert D >= int(S[(2*R-10)**2])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--quick', action='store_true')
    args = parser.parse_args()
    check_analytic_constants()
    check_exact_convolution()
    check_parity_endpoints()
    check_closest_pair()
    flags, S = sums_two_squares(4*128*128)
    check_parity_distance_support(flags)
    check_matching_gadget()
    check_off_center_restorations(S, args.quick)
    check_sparse_samples(S, args.quick)
    print('ALL CHECKS PASSED. The universal planar disk criterion remains unresolved.')


if __name__ == '__main__':
    main()
