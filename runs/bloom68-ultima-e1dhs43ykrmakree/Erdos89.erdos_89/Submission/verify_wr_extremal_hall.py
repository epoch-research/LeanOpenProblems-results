#!/usr/bin/env python3
"""Small exact palette / Hall audit for the extremal WR investigation.

Five palettes are searched globally using all two-anchor circle intersections.
Two more palettes check modular matchings (a 7 by 7 square and its shear).
An eighth palette checks only the full-fiber Cauchy calculation at three pins.
The clique enumeration is independently cross-checked by NetworkX Bron--Kerbosch.
All equality tests use integers and Fraction; no floating point is used.
This does not prove WR or classify F(s)-maximizers.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd, lcm


def dot(x, y, G):
    a, b, c = G
    return a*x[0]*y[0] + b*(x[0]*y[1]+x[1]*y[0]) + c*x[1]*y[1]


def sub(x, y):
    return x[0]-y[0], x[1]-y[1]


def add(x, y):
    return x[0]+y[0], x[1]+y[1]


def norm(x, G):
    return dot(x, x, G)


def dist(x, y, G):
    return norm(sub(x, y), G)


def line_key(a, b, c):
    a, b, c = map(F, (a, b, c))
    den = lcm(a.denominator, b.denominator, c.denominator)
    A, B, C = int(a*den), int(b*den), int(c*den)
    d = gcd(gcd(A, B), C)
    assert d and (A or B)
    if A < 0 or (A == 0 and B < 0):
        d = -d
    return A//d, B//d, C//d


def bisector(x, y, G):
    a, b, c = G
    u, v = sub(y, x)
    return line_key(2*(a*u+b*v), 2*(b*u+c*v), norm(y, G)-norm(x, G))


def reflect(x, axis, G):
    a, b, c = G
    A, B, C = axis
    U, V = c*A-b*B, a*B-b*A
    z = F(2*(A*x[0]+B*x[1]-C), A*U+B*V)
    return x[0]-z*U, x[1]-z*V


def stats(P, G):
    P = tuple(sorted(P))
    n = len(P)
    pins = [Counter() for _ in P]
    ws = Counter()
    for i, j in combinations(range(n), 2):
        s = dist(P[i], P[j], G)
        pins[i][s] += 1
        pins[j][s] += 1
        ws[bisector(P[i], P[j], G)] += 2
    S = frozenset().union(*(set(f) for f in pins))
    D = len(S)
    B = F(n*(n-1)-sum(map(len, pins)), D)
    axes = {}
    R = 0
    for ell, w in ws.items():
        A, BB, C = ell
        m = sum(A*x+BB*y == C for x, y in P)
        axes[ell] = (m, w)
        R += m*min(w, m*(m-1))
    # Independent full-fiber witness mass and reflection counts.
    mass = defaultdict(F)
    Pset = set(P)
    for i, p in enumerate(P):
        fibers = defaultdict(list)
        for x in P:
            if x != p:
                fibers[dist(x, p, G)].append(x)
        for s, fiber in fibers.items():
            for x, y in combinations(fiber, 2):
                mass[bisector(x, y, G)] += F(2, D*len(fiber))
    assert sum(mass.values(), F()) == B
    for ell, (m, w) in axes.items():
        rP = {reflect(x, ell, G) for x in P}
        assert len(Pset & rP) == m+w
        assert sum(reflect(x, ell, G) in Pset and reflect(x, ell, G) != x
                   for x in P) == w
    return dict(n=n, S=S, D=D, B=B, R=R, axes=axes, mass=mass)


def fast_R(P, G):
    P = tuple(P)
    ws = Counter(bisector(x, y, G) for x, y in combinations(P, 2))
    total = 0
    for (a, b, c), unordered_w in ws.items():
        m = sum(a*x+b*y == c for x, y in P)
        total += m*min(2*unordered_w, m*(m-1))
    return total


def radical(q):
    """Return c,d with sqrt(q)=c sqrt(d), c rational and d squarefree."""
    q = F(q)
    assert q > 0
    z = q.numerator*q.denominator
    c, d = 1, 1
    r = 2
    while r*r <= z:
        e = 0
        while z % r == 0:
            e += 1
            z //= r
        c *= r**(e//2)
        if e % 2:
            d *= r
        r += 1
    if z > 1:
        d *= z
    c = F(c, q.denominator)
    assert c*c*d == q
    return c, d


def maximum_cliques(adj):
    """Exact bitset branch and bound, retaining every maximum clique."""
    n = len(adj)
    best, answers = 0, []
    def search(chosen, possible):
        nonlocal best, answers
        if len(chosen)+possible.bit_count() < best:
            return
        if not possible:
            if len(chosen) > best:
                best, answers = len(chosen), [tuple(chosen)]
            elif len(chosen) == best:
                answers.append(tuple(chosen))
            return
        while possible:
            if len(chosen)+possible.bit_count() < best:
                return
            bit = possible & -possible
            v = bit.bit_length()-1
            possible ^= bit
            search(chosen+[v], possible & adj[v])
    search([], (1 << n)-1)
    # Independent combinatorial implementation, with the same exact graph.
    import networkx as nx
    graph = nx.Graph()
    graph.add_nodes_from(range(n))
    graph.add_edges_from((i, j) for i in range(n) for j in range(i+1, n)
                         if adj[i] >> j & 1)
    other = list(nx.find_cliques(graph)) if n else [()]
    other_best = max(map(len, other))
    assert other_best == best
    assert {tuple(sorted(c)) for c in other if len(c) == best} == set(answers)
    return best, answers


def isometry_key(P, G):
    """Complete exact isometry invariant, by all minimum-length anchor frames.

    In each frame retain normalized horizontal coordinates, signs of heights,
    and squared heights. The anchor's actual squared length is also retained.
    """
    P = tuple(P)
    tmin = min(dist(x, y, G) for x, y in combinations(P, 2))
    signatures = []
    for a in P:
        for b in P:
            if a == b or dist(a, b, G) != tmin:
                continue
            u = sub(b, a)
            for orientation in (1, -1):
                points = []
                for z in P:
                    v = sub(z, a)
                    x = dot(u, v, G)/tmin
                    y2 = norm(v, G)/tmin-x*x
                    det = u[0]*v[1]-u[1]*v[0]
                    sign = orientation*((det > 0)-(det < 0))
                    assert (y2 == 0) == (sign == 0)
                    points.append((x, sign, y2))
                signatures.append(tuple(sorted(points)))
    return tmin, min(signatures)


def palette_maxima(S):
    """Global maximum, not just a search inside an a priori coordinate box.

    Anchor squared length t ranges over ALL of S. Each additional point is a
    circle intersection for radii r,s in S. Rational palettes split the
    noncollinear candidates by their height square class: two distinct classes
    cannot have a rational squared mutual distance. Collinear candidates are
    included in each block. The finite candidate search is therefore complete.
    """
    S = frozenset(map(F, S))
    global_best = 2
    representatives = {}
    anchor_best = []
    for t in sorted(S):
        blocks = defaultdict(set)
        collinear = set()
        for r, s in product(S, repeat=2):
            x = (r+t-s)/(2*t)
            q = r/t-x*x
            if q < 0:
                continue
            if q == 0:
                collinear.add((x, F(0)))
            else:
                c, d = radical(q)
                blocks[d].update(((x, c), (x, -c)))
        if not blocks:
            blocks[1] = set()
        local_best = 2
        for d, pts in sorted(blocks.items()):
            G = (t, F(0), t*d)
            candidates = sorted(pts | collinear)
            anchors = {(F(0), F(0)), (F(1), F(0))}
            assert not (anchors & set(candidates))
            for x in candidates:
                assert all(dist(x, a, G) in S for a in anchors)
            adj = [0]*len(candidates)
            for i, j in combinations(range(len(candidates)), 2):
                if dist(candidates[i], candidates[j], G) in S:
                    adj[i] |= 1 << j
                    adj[j] |= 1 << i
            size, cliques = maximum_cliques(adj)
            size += 2
            local_best = max(local_best, size)
            if size > global_best:
                global_best, representatives = size, {}
            if size == global_best:
                for clique in cliques:
                    P = frozenset(anchors | {candidates[i] for i in clique})
                    assert len(P) == global_best
                    assert all(dist(x, y, G) in S for x, y in combinations(P, 2))
                    representatives[isometry_key(P, G)] = (P, G)
        anchor_best.append((t, local_best))
    return global_best, list(representatives.values()), anchor_best


def audit_motion(P, Q, G, S, Rmax, axis=None):
    P, Q = frozenset(P), frozenset(Q)
    assert len(P) == len(Q)
    assert all(dist(x, y, G) in S for x, y in combinations(Q, 2))
    A, B = sorted(P-Q), sorted(Q-P)
    t = len(A)
    assert len(B) == t
    neighborhoods = []
    for b in B:
        neighborhoods.append(sum(1 << i for i, a in enumerate(A)
                                 if dist(a, b, G) not in S))
    unions = [0]*(1 << t)
    out = Counter(motions=1, nonempty=(t > 0), complete=(t > 0 and all(
        mask == (1 << t)-1 for mask in neighborhoods)))
    oldR = fast_R(P, G)
    if axis is not None:
        a, b, c = axis
        oldm = sum(a*x+b*y == c for x, y in P)
        oldw = sum(reflect(x, axis, G) in P and reflect(x, axis, G) != x for x in P)
        assert t == len(P)-oldm-oldw
        oldterm = oldm*min(oldw, oldm*(oldm-1))
    for mask in range(1, 1 << t):
        bit = mask & -mask
        j = bit.bit_length()-1
        bad = unions[mask ^ bit] | neighborhoods[j]
        unions[mask] = bad
        assert bad.bit_count() >= mask.bit_count(), ('Hall deficiency', P, Q, mask)
        if bad.bit_count() != mask.bit_count():
            continue
        Y = {B[j] for j in range(t) if mask >> j & 1}
        N = {A[i] for i in range(t) if bad >> i & 1}
        mixed = (P-N) | Y
        assert len(mixed) == len(P)
        assert all(dist(x, y, G) in S for x, y in combinations(mixed, 2))
        newR = fast_R(mixed, G)
        assert newR <= Rmax
        if mask != (1 << t)-1:
            out['proper_tight'] += 1
            out['R_up'] += newR > oldR
            out['R_down'] += newR < oldR
            out['R_same'] += newR == oldR
            out['noncongruent'] += isometry_key(mixed, G) != isometry_key(P, G)
        if axis is not None:
            newm = sum(a*x+b*y == c for x, y in mixed)
            neww = sum(reflect(x, axis, G) in mixed and reflect(x, axis, G) != x
                       for x in mixed)
            assert newm == oldm
            assert neww == oldw + 2*len({reflect(y, axis, G) for y in Y}-N)
            if oldw >= oldm*(oldm-1):
                assert newm*min(neww, newm*(newm-1)) == oldterm
    return out


def audit_palette(S):
    maximum, reps, anchor_best = palette_maxima(S)
    data = [(P, G, stats(P, G)) for P, G in reps]
    Rmax = max(d['R'] for _, _, d in data)
    print('PALETTE', sorted(S), 'global maximum', maximum,
          'isometry classes', len(reps),
          'R values', sorted({d['R'] for _, _, d in data}), flush=True)
    print('  all-anchor maxima:', [(str(t), n) for t, n in anchor_best], flush=True)
    reflection_counts, translation_counts = Counter(), Counter()
    for P, G, d in data:
        assert d['S'] <= set(map(F, S))
        assert fast_R(P, G) == d['R']
        for ell, (m, w) in d['axes'].items():
            if m >= 2:
                Q = {reflect(x, ell, G) for x in P}
                reflection_counts.update(audit_motion(P, Q, G, set(map(F, S)), Rmax, ell))
        translations = {sub(x, y) for x in P for y in P if x != y}
        for v in translations:
            Q = {add(x, v) for x in P}
            translation_counts.update(audit_motion(P, Q, G, set(map(F, S)), Rmax))
        # Exact generic motions: complete forbidden graphs, not a tolerance test.
        v = (F(1, 101), F(1, 103))
        Q = {add(x, v) for x in P}
        generic_t = audit_motion(P, Q, G, set(map(F, S)), Rmax)
        assert generic_t['complete'] == 1 and generic_t['proper_tight'] == 0
        ell = (101, 0, 1)
        Q = {reflect(x, ell, G) for x in P}
        generic_r = audit_motion(P, Q, G, set(map(F, S)), Rmax, ell)
        assert generic_r['complete'] == 1 and generic_r['proper_tight'] == 0
    print('  two-center witness reflections:', dict(reflection_counts), flush=True)
    print('  supported nonzero translations:', dict(translation_counts), flush=True)
    return maximum, reps, Rmax


def rank_mod(rows, p):
    a = [[int(x) % p for x in row] for row in rows]
    rank = 0
    for col in range(len(a[0])):
        pivot = next((j for j in range(rank, len(a)) if a[j][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        inv = pow(a[rank][col], -1, p)
        a[rank] = [x*inv % p for x in a[rank]]
        for j in range(len(a)):
            if j != rank and a[j][col]:
                c = a[j][col]
                a[j] = [(x-c*y) % p for x, y in zip(a[j], a[rank])]
        rank += 1
    return rank


def modq(x, p):
    x = F(x)
    assert x.denominator % p != 0
    return x.numerator*pow(x.denominator, -1, p) % p


def color(x, p):
    return modq(x[0], p), modq(x[1], p)


def check_modular_motion(P, Q, S, p):
    A, B = P-Q, Q-P
    ca = {color(a, p): a for a in A}
    cb = {color(b, p): b for b in B}
    assert len(ca) == len(A) and len(cb) == len(B)
    assert ca.keys() == cb.keys()
    for c in ca:
        d = dist(ca[c], cb[c], (F(1), F(0), F(1)))
        assert modq(d, p) == 0
        assert d not in S
    return len(A)


def modular_check(p, K=0):
    P = frozenset((F(x), F(K*x+y)) for x, y in product(range(p), repeat=2))
    G = (F(1), F(0), F(1))
    S = frozenset(dist(x, y, G) for x, y in combinations(P, 2))
    assert all(s.denominator == 1 and s.numerator % p for s in S)
    H = [[2*dot(x, y, G) for y in sorted(P)] for x in sorted(P)]
    assert rank_mod(H, p) == 2
    assert len({tuple(int(t) % p for t in row) for row in H}) == p*p
    # Every line through two actual points, not merely every witness axis.
    lines = set()
    for x, y in combinations(P, 2):
        u, v = sub(y, x)
        lines.add(line_key(v, -u, v*x[0]-u*x[1]))
    bisectors = {bisector(x, y, G) for x, y in combinations(P, 2)}
    for ell in lines | bisectors:
        Q = frozenset(reflect(x, ell, G) for x in P)
        check_modular_motion(P, Q, S, p)
        a, b, c = ell
        m = sum(a*x+b*y == c for x, y in P)
        w = len(P & Q)-m
        assert w <= p*p-p
        assert len(P-Q) >= p-m
    translations = {sub(x, y) for x in P for y in P if x != y}
    for v in translations:
        Q = frozenset(add(x, v) for x in P)
        check_modular_motion(P, Q, S, p)
    # Denominator divisible by p: all cross distances have negative p valuation.
    Q = frozenset(add(x, (F(1, p), F(0))) for x in P)
    assert not P & Q
    assert all(dist(a, b, G).denominator % p == 0 for a in P for b in Q)
    print('MODULAR CHECK (p,K) =', (p, K), ':', len(lines), 'two-point lines,',
          len(bisectors), 'endpoint bisectors,', len(translations),
          'supported translations; all color matchings passed.', flush=True)


def counterexample_and_cap_check():
    # Hall really can detect a missing point: it is not automatic for every P.
    P = frozenset(map(lambda x: tuple(map(F, x)), ((0, 0), (1, 0), (0, 1))))
    G = (F(1), F(0), F(1))
    ell = (2, 0, 1)
    Q = frozenset(reflect(x, ell, G) for x in P)
    A, B = P-Q, Q-P
    assert len(A) == len(B) == 1
    assert dist(next(iter(A)), next(iter(B)), G) in {F(1), F(2)}
    print('CONTROL: the three-corner square has an exact singleton Hall deficiency.', flush=True)
    # Exhaustive reflected exchange identity on subsets of the 3x3 square,
    # all using ONE fixed allowed palette, not a sweep of new palettes.
    grid = tuple((F(x), F(y)) for x, y in product(range(3), repeat=2))
    fixed_palette = {F(1), F(2), F(4), F(5), F(8)}
    checks = 0
    for mask in range(1, 1 << len(grid)):
        P = frozenset(grid[i] for i in range(len(grid)) if mask >> i & 1)
        for ell in ((1, 0, 1), (1, -1, 0), (1, 2, 2)):
            Q = frozenset(reflect(x, ell, G) for x in P)
            A, B = sorted(P-Q), sorted(Q-P)
            if len(B) > 7:
                continue
            S = fixed_palette
            a, b, c = ell
            m = sum(a*x+b*y == c for x, y in P)
            w = len(P & Q)-m
            for ymask in range(1 << len(B)):
                Y = {B[j] for j in range(len(B)) if ymask >> j & 1}
                N = {x for x in A if any(dist(x, y, G) not in S for y in Y)}
                mixed = (P-N) | Y
                assert all(dist(x, y, G) in S for x, y in combinations(mixed, 2))
                mm = sum(a*x+b*y == c for x, y in mixed)
                ww = sum(reflect(x, ell, G) in mixed and reflect(x, ell, G) != x
                         for x in mixed)
                assert mm == m
                assert ww == w+2*len({reflect(y, ell, G) for y in Y}-N)
                if w >= m*(m-1):
                    assert mm*min(ww, mm*(mm-1)) == m*min(w, m*(m-1))
                checks += 1
    print('EXCHANGE IDENTITY:', checks, 'exact mixed-set checks, including nonmaximal sets.', flush=True)


def shear_geometry_checks():
    # Check the constants in the rotated-box overlap construction without
    # enumerating any large palette or point set. Scaled rotated coordinates
    # are Xbar=x+K*y, Ybar=-K*x+y, so all tests remain rational.
    assert 2*9216*4320**2 <= 2**40
    assert F(1, 64)+F(2, 5)/16 <= F(1, 16)
    assert F(1, 6)-F(2, 5)/16 > F(1, 8)
    assert F(1, 5)+F(2, 5)/16 < F(1, 4)
    tests = 0
    for K in (2, 3, 7):
        q = K*K+1
        for a, b in ((-K, 1), (1-3*K, 3)):
            alpha, beta = a+K*b, -K*a+b
            assert beta > 0 and gcd(a, b) == 1
            assert q*abs(alpha) <= 16*beta
            r = 200*beta
            for i0, j0 in ((0, 0), (r//128, r//32)):
                p0 = (F(i0), F(K*i0+j0))
                assert abs(p0[0]+K*p0[1]) <= F(r*q, 16)
                assert abs(-K*p0[0]+p0[1]) <= F(r, 8)
                # Actual occupancy from the two integer parameter intervals.
                lo, hi = None, None
                for start, step in ((i0, a), (j0, beta)):
                    lower, upper = sorted((F(-r-start, step), F(r-start, step)))
                    lower = -((-lower.numerator)//lower.denominator)
                    upper = upper.numerator//upper.denominator
                    lo = lower if lo is None else max(lo, lower)
                    hi = upper if hi is None else min(hi, upper)
                m = max(0, hi-lo+1)
                t = F(r, beta)
                assert m >= 65 and m <= 2*t+1
                R0 = r//(16*beta)
                S0 = (r*q)//(32*beta)
                ell = line_key(b, -a, b*p0[0]-a*p0[1])
                # The four corners imply containment of the whole pattern.
                for u, v in product((-R0, R0), (-S0, S0)):
                    z = (p0[0]+u*a-v*b, p0[1]+u*b+v*a)
                    assert abs(z[0]+K*z[1]) <= F(r*q, 2)
                    assert abs(-K*z[0]+z[1]) <= r
                    assert abs(z[0]) <= r and abs(z[1]-K*z[0]) <= r
                    rz = reflect(z, ell, (F(1), F(0), F(1)))
                    assert rz == (p0[0]+u*a+v*b, p0[1]+u*b-v*a)
                lower_w = (2*R0+1)*2*S0
                assert lower_w >= F(q*m*m, 4608)
                tests += 1
    print('SHEAR OVERLAP:', tests, 'exact rational construction / occupancy checks.', flush=True)

    # Eighth palette; only three pinned fibers, not an extremal clique search.
    p, K = 31, 2
    r = (p-1)//2
    P = {(i, K*i+j) for i, j in product(range(-r, r+1), repeat=2)}
    S = {i*i+(K*i+j)**2 for i, j in product(range(-2*r, 2*r+1), repeat=2)
         if i or j}
    D, n = len(S), len(P)
    E = set()
    for a in range((r+5)//6, r//5+1):
        for b in range(-(r//16), r//16+1):
            z = (a, K*a+b)
            E.add(z)
            E.add((-z[0], -z[1]))
    assert E and E == {(-x, -y) for x, y in E}
    for pin in ((0, -1), (0, 0), (0, 1)):
        assert all(add(pin, z) in P for z in E)
        k = Counter((x-pin[0])**2+(y-pin[1])**2 for x, y in P if (x, y) != pin)
        e = Counter(x*x+y*y for x, y in E)
        mass = sum((F(z*z, 2*D*k[s]) for s, z in e.items()), F())
        direct = F()
        for x in E:
            for y in E:
                if (x[0]+K*x[1])*(y[0]+K*y[1]) < 0 and x[0]**2+x[1]**2 == y[0]**2+y[1]**2:
                    s = x[0]**2+x[1]**2
                    direct += F(1, D*k[s])
        assert mass == direct
        assert mass >= F(len(E)**2, 2*D*(n-1))
    print('FULL-FIBER SHEAR CHECK: 3 pins, exact opposite-side weights and Cauchy bound.', flush=True)



def irrational_motion_checks():
    # Same 3x3-square palette as above. Distances are represented exactly as
    # rational_part + radical_coefficient*sqrt(d), d=2 or 3.
    P = tuple(product(range(3), repeat=2))
    S = {1, 2, 4, 5, 8}
    def strict_check(vertices, formula, expected_minimum):
        t = len(vertices)
        masks = []
        for x in vertices:
            mask = 0
            for i, a in enumerate(vertices):
                rational, radical = formula(a, x)
                allowed = radical == 0 and rational in S
                if not allowed:
                    mask |= 1 << i
            masks.append(mask)
        assert min(map(int.bit_count, masks)) == expected_minimum
        assert min(sum(bool(mask >> i & 1) for mask in masks) for i in range(t)) == expected_minimum
        unions = [0]*(1 << t)
        for subset in range(1, (1 << t)-1):
            bit = subset & -subset
            j = bit.bit_length()-1
            unions[subset] = unions[subset ^ bit] | masks[j]
            assert unions[subset].bit_count() > subset.bit_count()
    # Translation by (sqrt(2),0). All images are nonrational, so no overlap.
    def translated(a, x):
        u, v = a[0]-x[0], a[1]-x[1]
        return u*u+v*v+2, -2*u
    strict_check(P, translated, 8)
    # Reflection in y=sqrt(3)x. Matrix is [[-1/2,sqrt(3)/2],
    # [sqrt(3)/2,1/2]]. Only the origin has a rational image; remove it.
    vertices = tuple(x for x in P if x != (0, 0))
    def reflected(a, x):
        u, v = a
        i, j = x
        return u*u+v*v+i*i+j*j+u*i-v*j, -(u*j+v*i)
    strict_check(vertices, reflected, 7)
    print('IRRATIONAL MOTIONS: exact Q(sqrt(2)) translation and Q(sqrt(3))',
          'reflection; minimum forbidden degrees 8/9 and 7/8, strict Hall.', flush=True)


def allowed_palette_disconnection(reps):
    # This palette is an ALLOWED palette; the two maxima have different actual
    # palettes. It illustrates disconnected exchange classes, not a same-actual-
    # palette counterexample to R-selection.
    A = frozenset((F(i), F(j)) for i, j in product(range(3), repeat=2)
                  if (i, j) not in ((0, 0), (0, 2)))
    GA = (F(1), F(0), F(1))
    B = frozenset((F(i), F(j)) for i, j in
                  ((0, 0), (1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)))
    GB = (F(1), F(1, 2), F(1))
    assert {isometry_key(P, G) for P, G in reps} == {isometry_key(A, GA), isometry_key(B, GB)}
    assert fast_R(A, GA) == 34 and fast_R(B, GB) == 60
    def areas_squared(P, G):
        a, b, c = G
        vals = set()
        for x, y, z in combinations(P, 3):
            u, v = sub(y, x), sub(z, x)
            determinant = u[0]*v[1]-u[1]*v[0]
            if determinant:
                vals.add(F(determinant*determinant*(a*c-b*b), 4))
        return vals
    assert not areas_squared(A, GA) & areas_squared(B, GB)
    for P in (A, B):
        for x, y in combinations(P, 2):
            u = sub(y, x)
            assert sum(u[0]*(z[1]-x[1]) == u[1]*(z[0]-x[0]) for z in P) <= 3
    print('ALLOWED-PALETTE DISCONNECTION: R=34 and R=60 classes have cross-isometry',
          'intersection at most 3; no 7-point neutral exchange between them.', flush=True)


def main():
    expected = [({1}, 3), ({1, 2}, 4), ({1, 3, 4}, 7), ({1, 2, 4, 5, 8}, 9),
                ({1, 2, 3, 4, 5}, 7)]
    for S, n in expected:
        maximum, reps, _ = audit_palette(S)
        assert maximum == n
        if S == {1, 2, 3, 4, 5}:
            allowed_palette_disconnection(reps)
    modular_check(3)     # same palette as the fourth clique search
    modular_check(7)     # sixth palette
    modular_check(7, 2)  # seventh palette
    counterexample_and_cap_check()
    irrational_motion_checks()
    shear_geometry_checks()  # eighth palette only for the three fiber checks
    print('PASS: all finite claims checked exactly. No WR conclusion is asserted.', flush=True)


if __name__ == '__main__':
    main()
