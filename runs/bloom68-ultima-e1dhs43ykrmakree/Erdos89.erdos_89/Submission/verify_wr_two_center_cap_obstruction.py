#!/usr/bin/env python3
"""Exact checks for wr_two_center_cap_obstruction.md.

These finite checks neither prove nor disprove universal WR.  The asymptotic
claims are proved in the accompanying note.  No Lean files are modified.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd, isqrt, prod

from verify_wr_investigation import line_key


def data(P, G=(1, 0, 1)):
    P = list(dict.fromkeys(P))
    n = len(P)
    aa, bb, cc = G
    assert n >= 2 and aa > 0 and aa*cc > bb*bb
    def norm(x, y):
        return aa*x*x + 2*bb*x*y + cc*y*y
    norms = [norm(*p) for p in P]
    dist = [[0]*n for _ in P]
    pins = [Counter() for _ in P]
    orbits = defaultdict(list)
    for a, b in combinations(range(n), 2):
        x, y = P[a]; X, Y = P[b]
        dx, dy = X-x, Y-y
        s = norm(dx, dy)
        dist[a][b] = dist[b][a] = s
        pins[a][s] += 1; pins[b][s] += 1
        axis = line_key(2*(aa*dx+bb*dy), 2*(bb*dx+cc*dy),
                        norms[b]-norms[a])
        orbits[axis].append((a, b))
    palette = set().union(*(set(pin) for pin in pins))
    D = len(palette)
    B = F(n*(n-1)-sum(map(len, pins)), D)
    axes = {}
    for axis, pairs in orbits.items():
        A, BB, C = axis
        centers = [p for p, (x, y) in enumerate(P) if A*x+BB*y == C]
        m, w = len(centers), 2*len(pairs)
        assert w <= n-m
        rows = {}
        mass = F(0)
        for p in centers:
            labels = [dist[p][a] for a, b in pairs]
            assert all(dist[p][a] == dist[p][b] for a, b in pairs)
            r = Counter(labels)
            assert all(2*v <= pins[p][s] for s, v in r.items())
            z = sum((F(2, D*pins[p][s]) for s in labels), F())
            assert 0 <= z <= 1
            rows[p] = (labels, r, z)
            mass += z
        assert mass <= m
        axes[axis] = dict(centers=centers, pairs=pairs, m=m, w=w,
                          mass=mass, rows=rows)
    assert sum(ax['w'] for ax in axes.values()) == n*(n-1)
    assert sum((ax['mass'] for ax in axes.values()), F()) == B
    return P, dist, pins, palette, D, B, axes


def audit(P, G=(1, 0, 1), chi_square=True):
    P, dist, pins, palette, D, B, axes = data(P, G)
    n = len(P)
    H = sum((a['mass'] for a in axes.values() if a['m'] >= 2), F())
    assert B <= 2*H+n
    assert B*B <= 8*H*H+2*n*n
    for lam in (F(3, 2), F(2), F(3), F(7)):
        J = F()
        for ax in axes.values():
            m = ax['m']
            for p in ax['centers']:
                for a, b in ax['pairs']:
                    k = pins[p][dist[p][a]]
                    if k >= lam*m:
                        J += F(2, D*k)
        assert J <= F(n*(n-1), D)/lam
        assert B <= (lam*(B-J)+n)/(lam-1)
    for M in (1, 2, 4):
        low = sum((a['mass'] for a in axes.values() if a['m'] <= M), F())
        assert low*low <= F(M*n*n*(n-1), D)
    for ax in axes.values():
        q = len(ax['pairs'])
        collisions = 0
        for p, (labels, r, z) in ax['rows'].items():
            eta = sum((F(pins[p][s]-2*v, pins[p][s])
                       for s, v in r.items()), F())
            assert len(r)-D*z == eta
            assert 0 <= eta <= F(n-1-ax['w'], 3)
            collisions += sum(v*(v-1)//2 for v in r.values())
        assert collisions <= q*(q-1)//2
        for p, t in combinations(ax['centers'], 2):
            lp, rp, _ = ax['rows'][p]
            lt, rt, _ = ax['rows'][t]
            edges = set(zip(lp, lt))
            assert len(edges) == q
            assert q <= len(rp)*len(rt)
            # Equivalent exact integer check of nonnegative mutual information.
            assert prod(rp[s]*rt[u] for s, u in edges) <= q**q
            reciprocal = sum((F(1, pins[p][s]*pins[t][u])
                              for s, u in edges), F())
            rhs = F((n-1)**2, q*q)*reciprocal
            assert rhs >= 1
            if chi_square:
                direct = F()
                for s, kp in pins[p].items():
                    for u, kt in pins[t].items():
                        reference = F(kp*kt, (n-1)**2)
                        joint = F(1, q) if (s, u) in edges else F()
                        direct += (joint-reference)**2/reference
                assert 1+direct == rhs
    return n, D, B, axes


def full_palette_and_dp(P):
    """Full palette and full pinned supports; no restricted palette substituted."""
    S, dp_sum = set(), 0
    for x, y in P:
        pin = Counter((x-X)**2+(y-Y)**2 for X, Y in P if (X, Y) != (x, y))
        S.update(pin)
        dp_sum += len(pin)
    return S, dp_sum


def punctured_diagonal(L):
    m = isqrt(L)
    P = [(x, y) for x, y in product(range(L+1), repeat=2)
         if x != y or x < m]
    S, dp_sum = full_palette_and_dp(P)
    D, n = len(S), len(P)
    base = {x*x+y*y for x, y in product(range(L+1), repeat=2) if x or y}
    N = len(base)
    assert N-L <= D <= N
    w = L*(L+1)
    assert n == w+m
    h = F()
    for j in range(m):
        pin = Counter((x-j)**2+(y-j)**2 for x, y in P if (x, y) != (j, j))
        r = Counter((x-j)**2+(y-j)**2 for x, y in P if x < y)
        z = sum((F(2*v, D*pin[s]) for s, v in r.items()), F())
        assert len(r) >= N-2*j*(L+1)-L
        eta = sum((F(pin[s]-2*v, pin[s]) for s, v in r.items()), F())
        assert len(r)-D*z == eta <= F(m-1, 3)
        h += z
    lower = 1-F(L*m, N)-F(4*(m-1), 3*N)
    assert lower <= h/m <= 1
    B = F(n*(n-1)-dp_sum, D)
    print('punctured diagonal', dict(L=L, n=n, D=D, m=m, w=w,
          cap_ratio=float(F(w, m*(m-1))), axis_mass_over_m=float(h/m),
          rigorous_finite_lower=float(lower), B_over_n=float(B/n)), flush=True)


def rectangle_audit(L, H):
    P = list(product(range(-L, L+1), range(-H, H+1)))
    P, dist, pins, palette, D, B, axes = data(P)
    n = len(P)
    central = [p for p, (x, y) in enumerate(P)
               if 8*abs(x) <= L and 8*abs(y) <= H]
    E1, E2 = F(), F()
    cross_axes = set()
    for p in central:
        x, y = P[p]
        for s, k in pins[p].items():
            if not (L*L <= 16*s and 4*s <= L*L):
                continue
            fiber = [a for a in range(n) if dist[p][a] == s]
            left = [a for a in fiber if P[a][0] < x]
            right = [a for a in fiber if P[a][0] > x]
            assert len(left) == len(right) == k//2
            assert 2*len(left) == k
            E1 += F(k, 2*D)
            for a in left:
                for b in right:
                    dx = P[b][0]-P[a][0]; dy = P[b][1]-P[a][1]
                    assert L*abs(dy) <= 8*H*abs(dx)
                    axis = line_key(2*dx, 2*dy,
                                    P[b][0]**2+P[b][1]**2-
                                    P[a][0]**2-P[a][1]**2)
                    assert p in axes[axis]['centers']
                    cross_axes.add(axis)
                    E2 += F(2, D*k)
    assert E1 == E2
    H2 = sum((ax['mass'] for ax in axes.values() if ax['m'] >= 2), F())
    assert B <= 2*H2+n
    R = sum(ax['m']*min(ax['w'], ax['m']*(ax['m']-1))
            for ax in axes.values() if ax['m'] >= 2)
    tails = {}
    for T in (1, 2, 4, 8):
        tails[T] = sum((ax['mass'] for ax in axes.values()
                        if ax['m'] >= 2 and ax['w'] >= T*ax['m']**2), F())
    print('rectangle', dict(L=L, H=H, n=n, D=D,
          B_over_n=float(B/n), cross_annulus_mass=float(E1),
          cross_axes=len(cross_axes), overfull_mass_over_B={T: float(v/B)
          if B else 0 for T, v in tails.items()}, WR_ratio=float(B*B/(n*n+R))),
          flush=True)


def lattice_overlap_audit(L, H, p, v):
    px, py = p; a, b = v
    assert b > 0 and gcd(a, b) == 1 and L >= H
    assert 8*abs(px) <= L and 8*abs(py) <= H
    assert L*abs(a) <= 8*H*b
    N = a*a+b*b
    m = w = 0
    for x in range(-L, L+1):
        for y in range(-H, H+1):
            dx, dy = x-px, y-py
            if a*dy-b*dx == 0:
                m += 1
                continue
            X = (a*a-b*b)*dx+2*a*b*dy
            Y = 2*a*b*dx+(b*b-a*a)*dy
            if X % N == 0 and Y % N == 0:
                X, Y = px+X//N, py+Y//N
                w += -L <= X <= L and -H <= Y <= H
    assert m <= F(2*H, b)+1
    r, s = H//(16*b), L//(16*b)
    constructed = (2*r+1)*2*s
    assert w >= constructed
    if m >= 65:
        assert w >= F(L*m*m, 2304*H)
    print('bulk near-vertical overlap', dict(L=L, H=H, p=p, v=v, m=m, w=w,
          w_over_m_squared=float(F(w, m*m)), constructed=constructed), flush=True)


def large_annulus_audit(L, H):
    assert L >= 30 and H >= 16 and L >= 16*H
    central_count = (2*(L//8)+1)*(2*(H//8)+1)
    assert central_count >= F(L*H, 64)
    for px, py in ((0, 0), (L//8, H//8), (-L//8, -H//8)):
        left, right, full = Counter(), Counter(), Counter()
        for x in range(-L, L+1):
            for y in range(-H, H+1):
                dx, dy = x-px, y-py
                s = dx*dx+dy*dy
                if L*L <= 16*s and 4*s <= L*L:
                    assert 8*abs(dx) > L
                    full[s] += 1
                    (left if dx < 0 else right)[s] += 1
        assert left == right
        assert all(full[s] == 2*left[s] for s in full)
        endpoints = sum(full.values())
        assert endpoints >= F(L*H, 15)
        # D times the actual normalized opposite-side witness mass at this pin.
        weighted_numerator = sum((F(2*left[s]*right[s], k)
                                  for s, k in full.items()), F())
        assert weighted_numerator == F(endpoints, 2)
        print('large full-fiber annulus', dict(L=L, H=H, p=(px, py),
              endpoints=endpoints, mass_times_D=str(weighted_numerator)), flush=True)


def arithmetic_support_audit():
    harmonic = F()
    for L in range(1, 101):
        harmonic += F(1, L)
        representations = Counter(x*x+y*y for x, y in product(range(L+1), repeat=2))
        E = sum(k*k for k in representations.values())
        N = len(representations)-1
        assert E <= (L+1)**2+8*L*L*harmonic
        assert N >= F(L*L, 4+8*harmonic)
    print('Exact arithmetic support/energy lower bounds: L=1,...,100.', flush=True)


def main():
    checked = 0
    grid = list(product(range(3), repeat=2))
    for G in ((1, 0, 1), (2, 1, 2), (1, 0, 5)):
        for mask in range(1 << len(grid)):
            P = [p for i, p in enumerate(grid) if mask >> i & 1]
            if len(P) >= 2:
                audit(P, G)
                checked += 1
    print('Exact absorption/deficit/injectivity/collision/chi-square audits:', checked,
          flush=True)
    # Equilateral triangle: B=n and H_1=0, proving the additive n is necessary.
    n, D, B, axes = audit([(0, 0), (1, 0), (0, 1)], (2, 1, 2))
    H1 = sum((a['mass'] for a in axes.values() if a['m'] >= 2), F())
    assert (n, D, B, H1) == (3, 1, F(3), F(0))
    print('Sharp one-center additive constant: equilateral triangle checked.', flush=True)
    for L in (8, 16, 24, 32, 48):
        punctured_diagonal(L)
    for L, H in ((16, 1), (24, 1), (32, 2)):
        rectangle_audit(L, H)
    arithmetic_support_audit()
    large_annulus_audit(512, 32)
    large_annulus_audit(1024, 64)
    for L, H, p, v in (
        (512, 32, (0, 0), (0, 1)),
        (1024, 64, (0, 0), (1, 2)),
        (1024, 64, (64, 4), (1, 2)),
        (1024, 64, (-64, -4), (-1, 2)),
        (2048, 64, (0, 0), (0, 1)),
        (2048, 128, (128, 8), (1, 3)),
    ):
        lattice_overlap_audit(L, H, p, v)
    print('All exact checks passed. Universal WR remains unresolved.', flush=True)


if __name__ == '__main__':
    main()
