#!/usr/bin/env python3
"""Exact finite audits for pinned_degree_comparison_counterexample.md.

These checks do not extrapolate to the asymptotic theorem.  That theorem is
proved in the note, including the far-pin cone lemma and the two stated
standard arithmetic inputs.  No floating-point distance comparisons occur.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import gcd, isqrt


@lru_cache(None)
def r2(s):
    assert s > 0
    x, p, answer = s, 2, 4
    while p * p <= x:
        exponent = 0
        while x % p == 0:
            exponent += 1
            x //= p
        if p % 4 == 3 and exponent % 2:
            return 0
        if p % 4 == 1:
            answer *= exponent + 1
        p = 3 if p == 2 else p + 2
    if x > 1:
        if x % 4 == 3:
            return 0
        if x % 4 == 1:
            answer *= 2
    return answer


@lru_cache(None)
def H(X):
    X = int(X)
    return sum(r2(s) ** 2 for s in range(1, X + 1))


def grid_colors(M):
    colors = Counter()
    for x in range(-(M - 1), M):
        for y in range(-(M - 1), M):
            s = x*x + y*y
            if s:
                colors[s] += (M-abs(x)) * (M-abs(y))
    return colors


def exact_data(points, labels=None, check_wedges=False, M=None, bases=None,
               primes=None):
    n = len(points)
    assert len(set(points)) == n
    colors = Counter()
    degrees = []
    pin_I = []
    inter_vectors = Counter()
    wedge_checks = 0
    sx = sum(x for x, y in points)
    sy = sum(y for x, y in points)
    sq = sum(x*x+y*y for x, y in points)
    for i, p in enumerate(points):
        fibers = defaultdict(list)
        for j, q in enumerate(points):
            if i == j:
                continue
            dx, dy = q[0]-p[0], q[1]-p[1]
            s = dx*dx + dy*dy
            fibers[s].append(j)
            if labels is not None and labels[i] != labels[j]:
                inter_vectors[dx, dy] += 1
        k = {s: len(indices) for s, indices in fibers.items()}
        degrees.append(k)
        colors.update(k)
        pin_I.append(sum(v*(v-1) for v in k.values()))
        assert sum(k.values()) == n-1
        assert sum(s*v for s, v in k.items()) == (
            n*(p[0]*p[0]+p[1]*p[1])
            - 2*(p[0]*sx+p[1]*sy) + sq)
        if labels is not None:
            for indices in fibers.values():
                assert len({labels[j] for j in indices}) == 1
        if check_wedges:
            by_direction = Counter()
            for indices in fibers.values():
                for j in indices:
                    for ell in indices:
                        if j == ell:
                            continue
                        q, r = points[j], points[ell]
                        target = labels[j]
                        vx, vy = q[0]-r[0], q[1]-r[1]
                        g = gcd(abs(vx), abs(vy))
                        vx, vy = vx//g, vy//g
                        if vx < 0 or (vx == 0 and vy < 0):
                            vx, vy = -vx, -vy
                        by_direction[target, vx, vy] += 1
                        # Exact midpoint/bisector identity.
                        assert vx*(2*p[0]-q[0]-r[0]) + vy*(2*p[1]-q[1]-r[1]) == 0
                        # Direction lies in the cone determined by the target square.
                        b, prime = bases[target], primes[target]
                        f = (2*p[0]-2*b[0]-prime*(M-1),
                             2*p[1]-2*b[1]-prime*(M-1))
                        dot = vx*f[0] + vy*f[1]
                        assert dot*dot <= 2*prime*prime*(M-1)**2*(vx*vx+vy*vy)
                        wedge_checks += 1
            for (target, vx, vy), count in by_direction.items():
                # The explicit O(M^2/|v|^2) direction estimate, with slack.
                assert count*(vx*vx+vy*vy) <= 16*M*M
    E = sum(v*v for v in colors.values())
    I = sum(pin_I)
    F = sum(v*v for row in degrees for v in row.values())
    assert I == F - n*(n-1)
    assert sum(colors.values()) == n*(n-1)
    # n^2 Delta = sum_(p,s) (n k_ps - r_s)^2, including zero entries.
    if n <= 100:
        scaled_delta = sum((n*row.get(s, 0)-r)**2
                           for row in degrees for s, r in colors.items())
        assert scaled_delta == n*n*F - n*E
        assert n*n*(I+n*n) == n*E + scaled_delta + n*n*n
    return colors, E, I, pin_I, inter_vectors, wedge_checks


def audit_representations():
    counts = Counter()
    X = 8192
    R = isqrt(X)
    for x in range(-R, R+1):
        for y in range(-R, R+1):
            s = x*x+y*y
            if 0 < s <= X:
                counts[s] += 1
    for s in range(1, X+1):
        assert counts[s] == r2(s)
    for p in (3, 7, 11, 19, 43):
        for t in range(1, 257):
            assert r2(p*p*t) == r2(t)
    # The primitive-vector lower-density argument used in the proof.
    for R in (2, 4, 8, 16, 32, 64):
        primitive = sum(gcd(a, b) == 1 and max(a, b) > R//2
                        for a in range(1, R+1) for b in range(1, R+1))
        assert 10*primitive >= R*R  # 7/4-pi^2/6 > 1/10
    print('Representation formula: 8,192 exact norms; 1,280 inert-prime identities; primitive density passed.')


def audit_grids():
    for M in (3, 5, 8, 12):
        pts = [(a, b) for a in range(M) for b in range(M)]
        colors, E, I, ip, _, _ = exact_data(pts)
        assert colors == grid_colors(M)
        a = (M-1)//2
        lower = Fraction(H(a*a), 16) - Fraction(sum(r2(s) for s in range(1, a*a+1)), 4)
        assert min(ip) >= lower
        assert max(ip) <= H(2*M*M)
        assert 16*E >= M**4 * H(a*a)
        assert E <= M**4 * H(2*M*M)
        print(f'Grid M={M:2}: n={M*M:3}, D={len(colors):3}, I={I:8}, E={E:12}; uniform pin and energy bounds passed.')


def audit_construction():
    cases = [(2, 10, [11, 19], 4),
             (3, 40, [43, 47, 59], 4),
             (4, 40, [43, 47, 59, 67], 5),
             (5, 60, [67, 71, 79, 83, 103], 4),
             (2, 10, [11, 19], 12)]
    all_wedges = 0
    for m, T, primes, M in cases:
        assert len(primes) == m and len(set(primes)) == m
        assert all(T <= p <= 2*T and p % 4 == 3 for p in primes)
        B = [4*m*m*i+i*i for i in range(m)]
        for i in range(m):
            assert len({abs(B[i]-B[j]) for j in range(m)}) == m
        bases = [(32*T*M*b, 0) for b in B]
        pts, labels = [], []
        for i, (base, prime) in enumerate(zip(bases, primes)):
            for a in range(M):
                for b in range(M):
                    pts.append((base[0]+prime*a, base[1]+prime*b))
                    labels.append(i)
        data = exact_data(pts, labels, True, M, bases, primes)
        colors, E, I, ip, inter_vectors, wedges = data
        all_wedges += wedges
        n = len(pts)
        X = (200*T*M*m**3)**2
        assert max(colors) <= X
        assert max(inter_vectors.values())*T*T <= m*(m-1)*(M+T)**2
        if M >= T:
            assert max(inter_vectors.values())*T*T <= 4*m*m*M*M
        # Check the geometric d >= 50 M m^2 |i-j| bound without square roots.
        for p, i in zip(pts, labels):
            for j, (base, prime) in enumerate(zip(bases, primes)):
                if i == j:
                    continue
                f = (2*p[0]-2*base[0]-prime*(M-1),
                     2*p[1]-2*base[1]-prime*(M-1))
                assert f[0]*f[0]+f[1]*f[1] >= (
                    2*prime*50*M*m*m*abs(i-j))**2
        internal = Counter()
        grid = grid_colors(M)
        for prime in primes:
            for s, mult in grid.items():
                internal[prime*prime*s] += mult
        out = colors-internal
        assert sum(out.values()) == m*(m-1)*M**4
        Ein, Eout = sum(v*v for v in internal.values()), sum(v*v for v in out.values())
        assert E <= 2*(Ein+Eout)
        assert E >= m*sum(v*v for v in grid.values())
        print(f'Blocks m={m}, M={M:2}, T={T:2}: n={n:3}, D={len(colors):6}, '
              f'I={I:8}, E={E:12}, E/(nI)={float(Fraction(E,n*I)):.6f}, '
              f'pin range=[{min(ip)},{max(ip)}]; all exact checks passed.')
    print(f'Exact endpoint-block separation and primitive-direction audits: {all_wedges:,} ordered isosceles triples.')


def audit_translation_and_overlap():
    cases = [(10, [11, 19], 32), (10, [11, 19], 64),
             (40, [43, 47, 59], 128)]
    for T, primes, M in cases:
        grid = grid_colors(M)
        for p, q in combinations(primes, 2):
            counts = Counter(p*a-q*b for a in range(M) for b in range(M))
            assert max(counts.values()) <= 1+(M-1)//max(p, q)
            ri = {p*p*s: mult for s, mult in grid.items()}
            rj = {q*q*s: mult for s, mult in grid.items()}
            overlap = sum(mult*rj.get(s, 0) for s, mult in ri.items())
            sharp_cutoff = (2*M*M)//max(p*p, q*q)
            assert overlap <= M**4 * H(sharp_cutoff)
            assert overlap <= M**4 * H((2*M*M)//(T*T))
            for s in ri.keys() & rj.keys():
                assert s % (p*p*q*q) == 0
                t = s//(p*p*q*q)
                assert r2(p*p*t) == r2(q*q*t) == r2(t)
        print(f'Finite translation and internal-palette overlap bounds: M={M}, primes={primes}, passed.')


def audit_annuli():
    for R, eta in [(32, Fraction(1, 4)), (64, Fraction(1, 8)),
                   (128, Fraction(1, 16))]:
        upper = (1+eta)*R*R
        Q = isqrt(upper.numerator//upper.denominator)
        pts = [(x, y) for x in range(-Q, Q+1) for y in range(-Q, Q+1)
               if R*R <= x*x+y*y <= upper]
        n = len(pts)
        assert sum(x for x, y in pts) == sum(y for x, y in pts) == 0
        q = [x*x+y*y for x, y in pts]
        mean = Fraction(sum(q), n)
        variance = sum((v-mean)**2 for v in q)/n
        assert variance <= eta*eta*mean*mean
        print(f'Centroid annulus R={R}, eta={eta}, n={n}: symmetry and relative radial variance passed.')


if __name__ == '__main__':
    audit_representations()
    audit_grids()
    audit_construction()
    audit_translation_and_overlap()
    audit_annuli()
    print('ALL EXACT FINITE CHECKS PASSED. Asymptotic claims are proved separately in the note.')
