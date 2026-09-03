#!/usr/bin/env python3
"""Exact audits for CubePositiveHallCircuitAttempt.md.

No Ramsey conclusion is assumed. Small host relations include GOOD injections;
they are not represented as global countercolourings. Entropy comparisons use
rational coefficients of prime logarithms, not floating-point tolerances.
"""
from collections import Counter, defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations, permutations, product
from math import comb, lcm
from pathlib import Path
import hashlib
import random

RNG = random.Random(18190709)
COUNTS = Counter()
SPEC_HASH = '9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b'


def fall(n, r):
    if not 0 <= r <= n:
        return 0
    ans = 1
    for j in range(r):
        ans *= n-j
    return ans


@lru_cache(None)
def factors(n):
    assert n > 0
    ans = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            ans[p] = ans.get(p, 0)+1
            n //= p
        p += 1
    if n > 1:
        ans[n] = ans.get(n, 0)+1
    return ans


def add(*forms):
    ans = defaultdict(Q)
    for form in forms:
        for p, v in form.items():
            ans[p] += v
    return {p: v for p, v in ans.items() if v}


def scale(q, form):
    return {p: Q(q)*v for p, v in form.items() if q*v}


def logq(q):
    q = Q(q)
    assert q > 0
    return add(factors(q.numerator), scale(-1, factors(q.denominator)))


def entropy(counts):
    counts = [Q(n) for n in counts if n]
    n = sum(counts)
    return add(logq(n), *[scale(-v/n, logq(v)) for v in counts])


def nonnegative(form):
    den = lcm(*(v.denominator for v in form.values())) if form else 1
    pos = neg = 1
    for p, v in form.items():
        k = int(v*den)
        if k >= 0:
            pos *= p**k
        else:
            neg *= p**(-k)
    return pos >= neg


def cube(d):
    E = tuple(x for x in range(1 << d) if x.bit_count() % 2 == 0)
    O = tuple(x for x in range(1 << d) if x.bit_count() % 2 == 1)
    return E, O, {y: tuple(y ^ (1 << i) for i in range(d)) for y in O}


def union(sets):
    ans = set()
    for s in sets:
        ans.update(s)
    return ans


def nonempty_subsets(s):
    s = tuple(s)
    for r in range(1, len(s)+1):
        yield from combinations(s, r)


def minimal_circuit(lists, O):
    # Increasing cardinality plus fixed ties gives an inclusion-minimal set.
    for S in nonempty_subsets(O):
        T = union(lists[y] for y in S)
        if len(T) < len(S):
            return tuple(S), tuple(sorted(T))
    return None


def check_literal_cube(d, even_map, odd_map, edges):
    E, O, nb = cube(d)
    assert set(even_map) == set(E) and set(odd_map) == set(O)
    assert len(set(even_map.values())) == len(E)
    assert len(set(odd_map.values())) == len(O)
    # The row and column pools are disjoint host parts, even if indices coincide.
    images = {('A', a) for a in even_map.values()} | {('B', b) for b in odd_map.values()}
    assert len(images) == 1 << d
    assert all((even_map[x], odd_map[y]) in edges for y in O for x in nb[y])
    COUNTS['literal cube embeddings, all vertices and edges checked'] += 1
    COUNTS['required original cube edges checked'] += d*len(E)


def robust_extend(d, k, R, B, edges, lower_E, lower_O, delta):
    j = d-k
    m, q = 1 << (d-1), 1 << (k-1)
    E, O, nb = cube(d)
    Ek, Ok, nbk = cube(k)
    r = m-q
    D = (j+1)*q
    assert 1 <= k < d and len(R) == r
    assert len(B) >= m+d*delta
    rows = defaultdict(set)
    cols = defaultdict(set)
    for a, b in edges:
        rows[a].add(b)
        cols[b].add(a)
    assert all(len(set(B)-rows[a]) <= delta for a in R)
    assert set(lower_E) == set(Ek) and set(lower_O) == set(Ok)
    assert not set(lower_E.values()) & set(R)
    assert len(set(lower_E.values())) == q and len(set(lower_O.values())) == q
    assert all(len(rows[a] & set(B)) >= D+(d-1)*delta for a in lower_E.values())
    assert all(len(cols[b] & set(R)) >= j*q for b in lower_O.values())
    assert all((lower_E[x], lower_O[y]) in edges for y in Ok for x in nbk[y])

    # Low k bits are the smaller face; high j bits are the new coordinates.
    emap, omap = dict(lower_E), dict(lower_O)
    private_E = [(1 << (k+i)) | w for i in range(j) for w in Ok]
    private_O = [(1 << (k+i)) | w for i in range(j) for w in Ek]
    assert len(private_E) == len(private_O) == j*q
    used_R = set()
    for x in private_E:
        w = x & ((1 << k)-1)
        avail = (cols[omap[w]] & set(R))-used_R
        assert len(avail) >= j*q-len(used_R)
        a = min(avail)
        emap[x] = a
        used_R.add(a)
    other_E = [x for x in E if x not in emap]
    free_R = sorted(set(R)-used_R)
    assert len(other_E) == len(free_R) == r-j*q
    emap.update(zip(other_E, free_R))
    assert all((emap[x], omap[y]) in edges for y in lower_O for x in nb[y])

    used_B = set(omap.values())
    for t, y in enumerate(private_O):
        avail = set(B)-used_B
        for x in nb[y]:
            avail &= rows[emap[x]]
        assert len(avail) >= j*q-t
        b = min(avail)
        omap[y] = b
        used_B.add(b)
    other_O = [y for y in O if y not in omap]
    assert len(other_O) == m-D
    for y in other_O:
        assert all(x not in lower_E for x in nb[y])
        avail = set(B)-used_B
        for x in nb[y]:
            avail &= rows[emap[x]]
        assert avail
        b = min(avail)
        omap[y] = b
        used_B.add(b)
    check_literal_cube(d, emap, omap, edges)
    COUNTS['robust complete/near-complete reservoir extensions'] += 1
    if any(set(B)-rows[a] for a in R):
        COUNTS['extensions with genuinely missing reservoir edges'] += 1
    if any(set(R)-cols[b] for b in lower_O.values()):
        COUNTS['extensions with errors at the already embedded face columns'] += 1
    return emap, omap


def audit_robust_extensions():
    for d in range(2, 8):
        m = 1 << (d-1)
        for k in range(1, d):
            j, q = d-k, 1 << (k-1)
            R = tuple(range(m-q))
            for delta in range(4):
                B = tuple(range(m+d*delta+2))
                Ek, Ok, nbk = cube(k)
                lower_E = {x: len(R)+i for i, x in enumerate(Ek)}
                lower_O = {y: i for i, y in enumerate(Ok)}
                face_B = set(lower_O.values())
                for _ in range(12):
                    bad_per_col = Counter()
                    edges = set()
                    for a in R:
                        candidates = list(B)
                        RNG.shuffle(candidates)
                        bad = set()
                        for b in candidates:
                            if len(bad) == delta:
                                break
                            if b in face_B and bad_per_col[b] >= len(R)-j*q:
                                continue
                            bad.add(b)
                            bad_per_col[b] += 1
                        assert len(bad) == delta
                        edges.update((a, b) for b in B if b not in bad)
                    threshold = (j+1)*q+(d-1)*delta
                    for x, a in lower_E.items():
                        neigh = {lower_O[y] for y in Ok if x in nbk[y]}
                        options = list(set(B)-neigh)
                        RNG.shuffle(options)
                        neigh.update(options[:max(0, threshold-len(neigh))])
                        edges.update((a, b) for b in neigh)
                    robust_extend(d, k, R, B, edges, lower_E, lower_O, delta)


def greedy_dense_cube(d, A, B, edges):
    E, O, nb = cube(d)
    emap = dict(zip(E, A))
    rows = defaultdict(set)
    for a, b in edges:
        rows[a].add(b)
    omap = {}
    for y in O:
        avail = set(B)-set(omap.values())
        for x in nb[y]:
            avail &= rows[emap[x]]
        assert avail
        omap[y] = min(avail)
    check_literal_cube(d, emap, omap, edges)
    return emap, omap


def audit_global_complete_reservoir():
    for d in range(2, 8):
        m = 1 << (d-1)
        T = tuple(range(m-1))
        X = tuple(range(m-1, 2*m-1))
        B = tuple(range(m+d*(d-1)))
        cases = []
        if d == 2:
            cells = list(product(X, B))
            cases = [{cells[i] for i in range(len(cells)) if mask >> i & 1}
                     for mask in range(1 << len(cells))]
        else:
            for z in range(128):
                edges = set()
                for x in X:
                    deg = RNG.randrange(d) if z % 2 == 0 else RNG.randrange(len(B)+1)
                    edges.update((x, b) for b in RNG.sample(B, deg))
                cases.append(edges)
        for xb_red in cases:
            red = set(product(T, B)) | xb_red
            rows = {x: {b for xx, b in xb_red if xx == x} for x in X}
            good = [x for x in X if len(rows[x]) >= d]
            if good:
                x = good[0]
                b = min(rows[x])
                robust_extend(d, 1, T, B, red, {0: x}, {1: b}, 0)
                COUNTS['global complete reservoir red completions'] += 1
            else:
                blue = set(product(X, B))-xb_red
                greedy_dense_cube(d, X, B, blue)
                COUNTS['global complete reservoir complementary completions'] += 1


def onto(t, s):
    return sum((-1)**i*comb(s, i)*(s-i)**t for i in range(s+1))


def audit_drc():
    specs = [(3, 3, 1, 'all'), (3, 3, 2, 'all'),
             (5, 5, 2, 'random'), (6, 6, 3, 'random')]
    for a, b, k, mode in specs:
        q, t = 1 << (k-1), 2*k
        cells = list(product(range(a), range(b)))
        masks = range(1 << (a*b)) if mode == 'all' else range(180)
        for mask in masks:
            if mode == 'all':
                edges = {cells[i] for i in range(len(cells)) if mask >> i & 1}
            else:
                p = RNG.choice([Q(1, 4), Q(1, 2), Q(3, 4), Q(9, 10), Q(1)])
                edges = {cell for cell in cells if RNG.randrange(p.denominator) < p.numerator}
            rows = {x: {y for xx, y in edges if xx == x} for x in range(a)}
            def common(W):
                ans = set(range(b))
                for x in W:
                    ans &= rows[x]
                return ans
            bad = [W for W in combinations(range(a), k) if len(common(W)) < q]
            exp_size = sum(Q(len(rows[x]), b)**t for x in range(a))
            exp_bad = sum(Q(len(common(W)), b)**t for W in bad)
            sum_size = sum_bad = Q(0)
            possible = []
            for ss in range(1, min(t, b)+1):
                for Z in combinations(range(b), ss):
                    V = {x for x in range(a) if set(Z) <= rows[x]}
                    bad_in_V = [W for W in bad if set(W) <= V]
                    probability = Q(onto(t, ss), b**t)
                    sum_size += probability*len(V)
                    sum_bad += probability*len(bad_in_V)
                    possible.append((V, bad_in_V))
            assert (exp_size, exp_bad) == (sum_size, sum_bad)
            bound_bad = comb(a, k)*Q(max(0, q-1), b)**t
            assert exp_bad <= bound_bad
            COUNTS['exact DRC common-neighbour/bad-set moment identities'] += 1
            if exp_size-exp_bad < q:
                continue
            V, bad_in_V = max(possible, key=lambda p: len(p[0])-len(p[1]))
            assert len(V)-len(bad_in_V) >= q
            clean = set(V)
            for W in bad_in_V:
                if set(W) <= clean:
                    clean.remove(min(W))
            assert len(clean) >= q
            assert all(len(common(W)) >= q for W in combinations(clean, k))
            Ek, Ok, nb = cube(k)
            emap = dict(zip(Ek, sorted(clean)[:q]))
            omap = {}
            for y in Ok:
                avail = common(emap[x] for x in nb[y])-set(omap.values())
                assert avail
                omap[y] = min(avail)
            check_literal_cube(k, emap, omap, edges)
            COUNTS['DRC smaller-cube constructions'] += 1


def audit_incidence_and_fibres():
    for d, a, b, all_hosts in [(2, 3, 3, True), (3, 5, 4, False)]:
        E, O, nb = cube(d)
        m = len(E)
        injections = list(permutations(range(a), m))
        e_index = {x: i for i, x in enumerate(E)}
        cells = list(product(range(a), range(b)))
        runs = range(1 << (a*b)) if all_hosts else range(100)
        for mask in runs:
            if all_hosts:
                red = {cells[i] for i in range(a*b) if mask >> i & 1}
            else:
                p = RNG.choice([Q(1, 4), Q(1, 2), Q(3, 4)])
                red = {cell for cell in cells if RNG.randrange(p.denominator) < p.numerator}
            def is_c(x, v, c):
                return ((x, v) in red) == (c == 0)
            def data(f):
                lists = [{y: {v for v in range(b)
                              if all(is_c(f[e_index[x]], v, c) for x in nb[y])}
                          for y in O} for c in range(2)]
                keys = [minimal_circuit(L, O) for L in lists]
                return lists, tuple(keys) if all(k is not None for k in keys) else 'GOOD'
            fdata = {f: data(f) for f in injections}
            fibres = defaultdict(list)
            for f in injections:
                fibres[fdata[f][1]].append(f)
            assert add(logq(len(injections)), scale(-1, entropy(map(len, fibres.values())))) == \
                add(*[scale(Q(len(fam), len(injections)), logq(len(fam))) for fam in fibres.values()])
            COUNTS['actual-host whole-cover entropy identities, GOOD retained'] += 1
            for key, fam in fibres.items():
                if key == 'GOOD':
                    continue
                profiles = defaultdict(list)
                profile_domains = {}
                for f in fam:
                    lists, _ = fdata[f]
                    profile = []
                    demands = [{x: set() for x in E} for _ in range(2)]
                    for c in range(2):
                        S, T = key[c]
                        assert len(T) == len(S)-1
                        R = {v: {y for y in S if v in lists[c][y]} for v in T}
                        assert all(len(union(R[v] for v in W)) >= len(W)+1
                                   for W in nonempty_subsets(T))
                        assert all(len(R[v]) >= 2 for v in T)
                        assert all(len(union(lists[c][y] for y in Y)) >= len(Y)
                                   for Y in nonempty_subsets(S) if len(Y) < len(S))
                        for v in T:
                            W = union(nb[y] for y in R[v])
                            assert len(W) >= 2*d-2
                            for x in W:
                                demands[c][x].add(v)
                            COUNTS['full positive candidate-neighbourhood incidences'] += len(W)
                        profile.append(tuple((v, tuple(sorted(R[v]))) for v in T))
                    profile = tuple(profile)
                    domains = {}
                    for x in E:
                        assert not demands[0][x] & demands[1][x]
                        domains[x] = {u for u in range(a)
                                      if all(is_c(u, v, c) for c in range(2) for v in demands[c][x])}
                        assert f[e_index[x]] in domains[x]
                    profile_domains[profile] = domains
                    profiles[profile].append(f)
                    # No global reservoir cap is assumed on these finite hosts.
                    # Check only the exact implication from full incidence load to host degree.
                    for errors in range(3):
                        Dhost = set()
                        heavy = set()
                        for c in range(2):
                            S, T = key[c]
                            if not T:
                                continue
                            Dhost |= {u for u in range(a)
                                      if sum(not is_c(u, v, c) for v in T) <= errors}
                            heavy |= {x for x in E if len(demands[c][x]) >= len(T)-errors}
                        assert all(f[e_index[x]] in Dhost for x in heavy)
                        COUNTS['full-incidence heavy-load to fixed host-pool implications'] += 1
                Ekey = logq(Q(len(injections), len(fam)))
                avg_refined = {}
                avg_positive_plus_slack = {}
                for profile, pfam in profiles.items():
                    domains = profile_domains[profile]
                    pos_count = sum(all(f[e_index[x]] in domains[x] for x in E) for f in injections)
                    assert pos_count >= len(pfam) > 0
                    probability = Q(len(pfam), len(fam))
                    loss = logq(Q(len(injections), pos_count))
                    slack = logq(Q(pos_count, len(pfam)))
                    avg_refined = add(avg_refined, scale(probability, logq(Q(len(injections), len(pfam)))))
                    avg_positive_plus_slack = add(avg_positive_plus_slack, scale(probability, add(loss, slack)))
                    COUNTS['rectangular positive-domain permanents counted exactly'] += 1
                Hprofile = entropy(map(len, profiles.values()))
                assert avg_refined == avg_positive_plus_slack == add(Ekey, Hprofile)
                COUNTS['exact full-profile entropy/refinement ledgers'] += 1
                if len(profiles) > 1:
                    COUNTS['fibres with a nonzero full-profile information tax'] += 1
            # Fixed anchor subsets, pinned BEFORE sampling the injection.
            for t in range(1, min(2, b)+1):
                for anchors in combinations(range(b), t):
                    for c in range(2):
                        A0 = [u for u in range(a) if all(is_c(u, v, c) for v in anchors)]
                        if len(A0) < m:
                            continue
                        pinned = [f for f in injections if set(f) <= set(A0)]
                        assert len(pinned) == fall(len(A0), m)
                        pin_key_counts = Counter(fdata[f][1] for f in pinned)
                        Epin = logq(Q(len(injections), len(pinned)))
                        avg = add(*[scale(Q(n, len(pinned)), logq(Q(len(injections), n)))
                                    for n in pin_key_counts.values()])
                        assert avg == add(Epin, entropy(pin_key_counts.values()))
                        for f in pinned:
                            L, _ = fdata[f]
                            circ = minimal_circuit(L[c], O)
                            if circ is not None:
                                S, T = circ
                                assert len(S) >= t+1 and set(anchors) <= set(T)
                                if len(S) == t+1:
                                    assert set(T) == set(anchors)
                                    assert all(L[c][y] == set(anchors) for y in S)
                        COUNTS['fixed-anchor exact entropy rebasing/minimality checks'] += 1


def audit_nontrivial_profile_information():
    # One actual 8-by-4 cross-colour relation. The five ordinary host rows
    # are twins, so each assignment of the other three rows represents exactly
    # 5! full injections. This exhausts all 8! injections, not a selected fibre.
    d, a, b = 4, 8, 4
    E, O, nb = cube(d)
    ix = {x: i for i, x in enumerate(E)}
    multiplicity = fall(5, 5)
    ambient = []
    fibres = defaultdict(lambda: defaultdict(list))
    domains = {}
    def is_c(u, v, c):
        return (v == 0 or u != v-1) == (c == 0)
    for positions in permutations(range(a), 3):
        f = [None]*a
        for u, pos in enumerate(positions):
            f[pos] = u
        for pos, u in zip([i for i in range(a) if f[i] is None], range(3, a)):
            f[pos] = u
        f = tuple(f)
        ambient.append(f)
        lists = [{y: {v for v in range(b) if all(is_c(f[ix[x]], v, c) for x in nb[y])}
                  for y in O} for c in range(2)]
        key = tuple(minimal_circuit(L, O) for L in lists)
        assert all(k is not None for k in key)
        profile = tuple(tuple((v, tuple(y for y in S if v in lists[c][y])) for v in T)
                        for c, (S, T) in enumerate(key))
        demand = [{x: set() for x in E} for _ in range(2)]
        for c, incidences in enumerate(profile):
            for v, rows in incidences:
                for x in union(nb[y] for y in rows):
                    demand[c][x].add(v)
        D = {x: {u for u in range(a) if all(is_c(u, v, c)
                                         for c in range(2) for v in demand[c][x])} for x in E}
        assert all(f[ix[x]] in D[x] for x in E)
        domains[key, profile] = D
        fibres[key][profile].append(f)
    total = len(ambient)*multiplicity
    assert total == fall(a, a)
    key_sizes = [multiplicity*sum(map(len, profs.values())) for profs in fibres.values()]
    assert sum(key_sizes) == total
    assert add(logq(total), scale(-1, entropy(key_sizes))) == \
        add(*[scale(Q(n, total), logq(n)) for n in key_sizes])
    COUNTS['additional actual-host whole-cover entropy identities, type-compressed'] += 1
    for key, profiles in fibres.items():
        size = multiplicity*sum(map(len, profiles.values()))
        Ekey = logq(Q(total, size))
        Hprofile = entropy(multiplicity*len(pfam) for pfam in profiles.values())
        avg = {}
        for profile, pfam in profiles.items():
            D = domains[key, profile]
            z = multiplicity*sum(all(f[ix[x]] in D[x] for x in E) for f in ambient)
            exact = multiplicity*len(pfam)
            assert z >= exact > 0
            avg = add(avg, scale(Q(exact, size),
                                 add(logq(Q(total, z)), logq(Q(z, exact)))))
            COUNTS['rectangular positive-domain permanents counted exactly'] += 1
        assert avg == add(Ekey, Hprofile)
        assert len(profiles) > 1 and Hprofile
        COUNTS['exact full-profile entropy/refinement ledgers'] += 1
        COUNTS['fibres with a nonzero full-profile information tax'] += 1
    COUNTS['full injections represented in nontrivial-profile audit'] += total


def audit_occupancy_entropy():
    for a in range(2, 9):
        for m in range(1, min(a, 4)+1):
            ambient = list(permutations(range(a), m))
            for D in range(a+1):
                H = {f: sum(x < D for x in f) for f in ambient}
                for z in [1, 2, 3, 5]:
                    direct = Q(sum(z**H[f] for f in ambient), len(ambient))
                    hyper = sum(Q(comb(m, j)*fall(D, j)*fall(a-D, m-j), fall(a, m))*z**j
                                for j in range(m+1))
                    factorial_moments = sum(comb(m, j)*Q(fall(D, j), fall(a, j))*(z-1)**j
                                            for j in range(m+1))
                    assert direct == hyper == factorial_moments
                    assert direct <= (1+Q(D, a)*(z-1))**m
                    COUNTS['exact hypergeometric MGFs and without-replacement bounds'] += 1
                    families = [ambient, [ambient[0]], RNG.sample(ambient, max(1, len(ambient)//2))]
                    for fam in families:
                        mean = Q(sum(H[f] for f in fam), len(fam))
                        E = logq(Q(len(ambient), len(fam)))
                        rhs = add(scale(mean, logq(z)), scale(-1, logq(direct)))
                        assert nonnegative(add(E, scale(-1, rhs)))
                        COUNTS['exact no-refinement occupancy KL inequalities'] += 1


def audit_joint_tilted_prefix_prices():
    for a in range(3, 8):
        for m in range(2, min(4, a)+1):
            ambient = list(permutations(range(a), m))
            for _ in range(8):
                family = RNG.sample(ambient, RNG.randrange(1, len(ambient)+1))
                path = RNG.choice(family)
                for q0 in range(m):
                    prefix = path[:q0]
                    completions = [f for f in family if f[:q0] == prefix]
                    n = a-q0
                    s = min(2, m-q0)
                    pool = set(range(a))-set(prefix)
                    batch_space = list(permutations(sorted(pool), s))
                    counts = Counter(f[q0:q0+s] for f in completions)
                    denominator = sum(counts.values())
                    pi = {z: Q(w, denominator) for z, w in counts.items()}
                    delta = add(logq(fall(n, s)), scale(-1, entropy(counts.values())))
                    D = set(range(RNG.randrange(a+1)))
                    H = {z: len(set(z) & D) for z in batch_space}
                    mean = sum(pi[z]*H[z] for z in pi)
                    support = set(pi)
                    others = list(set(batch_space)-support)
                    RNG.shuffle(others)
                    relaxed_support = support | set(others[:len(others)//2])
                    for S in [set(batch_space), relaxed_support]:
                        for tilt in [1, 2, 5]:
                            W = sum(tilt**H[z] for z in S)
                            Z = Q(W, fall(n, s))
                            bound = add(scale(mean, logq(tilt)), scale(-1, logq(Z)))
                            tilted = {z: Q(tilt**H[z], W) for z in S}
                            remainder = add(*[scale(p, logq(p/tilted[z])) for z, p in pi.items()])
                            assert delta == add(bound, remainder)
                            assert nonnegative(remainder)
                            COUNTS['joint support/positive tilted-price identities at actual prefixes'] += 1
                    if len(set(counts.values())) > 1:
                        COUNTS['nonuniform completion-weighted prefix laws in joint-price audit'] += 1


def audit_reservoir_parameters():
    dims = list(range(2048, 4097)) + [8192, 16384, 32768, 65536]
    for d in dims:
        m = 1 << (d-1)
        pairs = [(1, 0), (d*d, 0), (1, 1), (1, d*d-1),
                 (d, d*d-d), (d*d//2, d*d-d*d//2)]
        h = RNG.randint(1, d*d)
        pairs.append((h, RNG.randint(0, d*d-h)))
        for h, e in pairs:
            delta = m//(4*d*d)
            q = 1 << ((h+8*d*d*e)-1).bit_length()
            k, j = q.bit_length(), d-q.bit_length()
            assert 1 <= k < d and q == 1 << (k-1)
            assert q >= h+(2*m*e)//(delta+1)
            assert d*delta <= m
            assert m-q-e >= j*q
            assert (j+1)*q+(d-1)*delta <= m//d+1
            assert m >= 2*q*(2*d)**(2*k)
            assert q*q <= m
            COUNTS['integer near-reservoir parameter instances'] += 1
    for ell in range(11, 161):
        assert (1 << ell)-1 >= 8*ell*ell+40*ell+50
        COUNTS['dyadic all-dimensional corollary base/induction numerical checks'] += 1


def main():
    spec = Path(__file__).with_name('Spec.lean')
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_HASH
    audit_robust_extensions()
    audit_global_complete_reservoir()
    audit_drc()
    audit_incidence_and_fibres()
    audit_nontrivial_profile_information()
    audit_occupancy_entropy()
    audit_joint_tilted_prefix_prices()
    audit_reservoir_parameters()
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_HASH
    print('All positive Hall-incidence and reservoir audits passed (integer/rational arithmetic).')
    for key, n in sorted(COUNTS.items()):
        print(f'{n:>10}  {key}')
    print('Spec.lean SHA-256:', SPEC_HASH)
    print('These checks do not prove the diffuse/global entropy surplus or R(Q_d)=O(2^d).')


if __name__ == '__main__':
    main()
