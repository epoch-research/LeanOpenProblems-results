#!/usr/bin/env python3
"""Independent finite/algebraic checks for CubeBlockAmplification.md.

These checks do not prove the missing uniform spectral transfer. No Lean file
is read as an axiom or modified. Large-dimension checks use logarithms, not an
attempt to construct an exponentially large host.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import ceil, comb, exp, factorial, log, log2, sqrt
from pathlib import Path
import hashlib
import random

import mpmath as mp
import numpy as np

SEED = 20260901
rng = random.Random(SEED)
ROOT = Path(__file__).resolve().parent
SPEC_HASH = '9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b'


def cube_edges(k):
    return [(x, x ^ (1 << j)) for x in range(1 << k)
            for j in range(k) if x < (x ^ (1 << j))]


def falling(n, r):
    if r > n:
        return 0
    z = 1
    for i in range(r):
        z *= n - i
    return z


def adjacency(n, es):
    a = [[0] * n for _ in range(n)]
    for x, y in es:
        a[x][y] = a[y][x] = 1
    return a


def embeddings(a, k):
    n, b = len(a), 1 << k
    if b > n:
        return []
    es = cube_edges(k)
    return [f for f in permutations(range(n), b)
            if all(a[f[x]][f[y]] for x, y in es)]


def lift_count(a, k, t):
    omega = embeddings(a, k)
    masks = [sum(1 << v for v in f) for f in omega]
    outer_n = 1 << t
    pred = [[x for x in range(y) if (x ^ y).bit_count() == 1]
            for y in range(outer_n)]
    comp = [[False] * len(omega) for _ in omega]
    for i, f in enumerate(omega):
        for j, g in enumerate(omega):
            comp[i][j] = not (masks[i] & masks[j]) and all(
                a[u][v] for u, v in zip(f, g))
    chosen = []

    def rec(y, used):
        if y == outer_n:
            return 1
        total = 0
        for j in range(len(omega)):
            if masks[j] & used:
                continue
            if not all(comp[j][chosen[x]] for x in pred[y]):
                continue
            chosen.append(j)
            total += rec(y + 1, used | masks[j])
            chosen.pop()
        return total

    return rec(0, 0)


def check_block_lifts():
    count = 0
    es4 = list(combinations(range(4), 2))
    for bits in range(1 << len(es4)):
        a = adjacency(4, [e for i, e in enumerate(es4) if bits >> i & 1])
        direct = len(embeddings(a, 2))
        assert lift_count(a, 1, 1) == direct
        assert lift_count(a, 0, 2) == direct
        count += 2
    hosts = [adjacency(8, cube_edges(3)),
             adjacency(8, combinations(range(8), 2))]
    for _ in range(3):
        hosts.append(adjacency(8, [e for e in combinations(range(8), 2)
                                   if rng.random() < .65]))
    for a in hosts:
        direct = len(embeddings(a, 3))
        for k, t in [(1, 2), (2, 1)]:
            assert lift_count(a, k, t) == direct
            count += 1
    print(f'Exact globally injective block-lift identities: {count} checks passed.')


def check_gram():
    hosts = [adjacency(4, combinations(range(4), 2)),
             adjacency(5, combinations(range(5), 2))]
    for _ in range(10):
        hosts.append(adjacency(5, [e for e in combinations(range(5), 2)
                                   if rng.random() < .65]))
    checks = 0
    nonzero = 0
    for a in hosts:
        omega = embeddings(a, 1)
        M = len(omega)
        if not M:
            continue
        W = [[int(set(f).isdisjoint(g) and all(a[x][y] for x, y in zip(f, g)))
              for g in omega] for f in omega]
        q = [F(sum(W[i][j] for i in range(M)), M) for j in range(M)]
        c = [[F(sum(W[i][j] * W[i][l] for i in range(M)), M)
              for l in range(M)] for j in range(M)]
        R = [[c[j][l] - q[j] * q[l] for l in range(M)] for j in range(M)]
        for t in [2, 3]:
            hist = Counter()
            for rows in product(range(M), repeat=t):
                z = sum(all(W[i][j] for i in rows) for j in range(M))
                hist[z] += 1
            mean = sum(F(z * n, M ** t) for z, n in hist.items())
            second = sum(F(z * z * n, M ** t) for z, n in hist.items())
            assert mean == sum(v ** t for v in q)
            assert second == sum(c[j][l] ** t for j in range(M) for l in range(M))
            aa = [v ** (t - 1) for v in q]
            linear = t * sum(aa[j] * R[j][l] * aa[l]
                             for j in range(M) for l in range(M))
            # Independently evaluate the same Gram term as a sum of squares.
            square = F(t, M) * sum(
                sum((F(W[i][j]) - q[j]) * aa[j] for j in range(M)) ** 2
                for i in range(M))
            assert linear == square and linear >= 0
            rem = F(0)
            for j in range(M):
                for l in range(M):
                    poly = sum((i + 1) * (q[j] * q[l]) ** i * c[j][l] ** (t - 2 - i)
                               for i in range(t - 1))
                    term = R[j][l] ** 2 * poly
                    assert term >= 0
                    rem += term
            assert second - mean ** 2 == linear + rem
            nonzero += int(second > mean ** 2)
            checks += 1
    print(f'Exact block-star moments and nonnegative Gram decomposition: {checks} checks '
          f'({nonzero} nonzero variances).')


def partial_bijections(b):
    for s in range(b + 1):
        for S in combinations(range(b), s):
            for T in combinations(range(b), s):
                for p in permutations(T):
                    yield dict(zip(S, p))


def requirements(k, t, n):
    b = 1 << k
    all_pairs = list(combinations(range(t * b + n), 2))
    index = {p: i for i, p in enumerate(all_pairs)}
    reqs = []
    for f in permutations(range(n), b):
        edges = []
        for j in range(t):
            for a in range(b):
                edges.append((j * b + a, t * b + f[a]))
        for a, c in cube_edges(k):
            edges.append(tuple(sorted((t * b + f[a], t * b + f[c]))))
        reqs.append(sum(1 << index[e] for e in edges))
    return reqs


def check_collision_formula():
    cases = [(1, 1, 3), (1, 2, 3), (1, 3, 4),
             (2, 1, 4), (2, 1, 5), (2, 2, 5)]
    pairs = 0
    for k, t, n in cases:
        b, e = 1 << k, len(cube_edges(k))
        reqs = requirements(k, t, n)
        counts = Counter((x | y).bit_count() for x in reqs for y in reqs)
        direct = sum(F(c, 1 << z) for z, c in counts.items())
        formula = F(0)
        for p in partial_bijections(b):
            fixed = sum(a == c for a, c in p.items())
            shared = sum(a in p and c in p and (p[a] ^ p[c]).bit_count() == 1
                         for a, c in cube_edges(k))
            exponent = 2 * (t * b + e) - t * fixed - shared
            formula += F(falling(n, 2 * b - len(p)), 1 << exponent)
        assert direct == formula
        mean = sum(F(1, 1 << x.bit_count()) for x in reqs)
        assert mean == F(falling(n, b), 1 << (t * b + e))
        pairs += len(reqs) ** 2
    # Enumerate every relevant host in the smallest nontrivial experiment.
    reqs = requirements(1, 1, 3)
    support = 0
    for x in reqs:
        support |= x
    pos = [i for i in range(support.bit_length()) if support >> i & 1]
    hosts = 1 << len(pos)
    s1 = s2 = 0
    for bits in range(hosts):
        host = sum(1 << p for i, p in enumerate(pos) if bits >> i & 1)
        z = sum(host & req == req for req in reqs)
        s1 += z
        s2 += z * z
    assert F(s1, hosts) == sum(F(1, 1 << x.bit_count()) for x in reqs)
    assert F(s2, hosts) == sum(F(1, 1 << (x | y).bit_count()) for x in reqs for y in reqs)
    print(f'Finite-population partial-bijection formula: {len(cases)} cases, '
          f'{pairs} embedding pairs, plus all {hosts} small random hosts passed.')


def partite_requirements(k, ell):
    b = 1 << k
    es = cube_edges(k)
    edge_index = {}
    for a, c in es:
        for x in range(ell):
            for y in range(ell):
                edge_index[(a, x, c, y)] = len(edge_index)
    maps = list(product(range(ell), repeat=b))
    reqs = [sum(1 << edge_index[(a, f[a], c, f[c])] for a, c in es) for f in maps]
    return maps, reqs, len(edge_index)


def check_partite_moments_and_sampler():
    moment_checks = 0
    for k, ell in [(1, 2), (1, 3), (2, 2), (2, 3)]:
        b, e = 1 << k, len(cube_edges(k))
        maps, reqs, _ = partite_requirements(k, ell)
        second = sum(F(1, 1 << (x | y).bit_count()) for x in reqs for y in reqs)
        mu = F(ell ** b, 1 << e)
        ratio = F(0)
        for mask in range(1 << b):
            s = mask.bit_count()
            es = sum((mask >> a & 1) and (mask >> c & 1) for a, c in cube_edges(k))
            ratio += F(1, ell) ** s * F(ell - 1, ell) ** (b - s) * (1 << es)
        assert second == mu * mu * ratio
        moment_checks += 1
    graph_count = 0
    for k, ell in [(1, 2), (1, 3), (2, 2)]:
        maps, reqs, variables = partite_requirements(k, ell)
        mu = F(len(maps), 1 << len(cube_edges(k)))
        hist = [Counter() for _ in maps]
        successes = 0
        for graph in range(1 << variables):
            valid = [i for i, req in enumerate(reqs) if graph & req == req]
            z = len(valid)
            if F(z) < mu / 2:
                continue
            successes += 1
            for i in valid:
                hist[i][z] += 1
        assert successes
        assert all(h == hist[0] for h in hist)
        mass = sum(F(number, z) for z, number in hist[0].items())
        assert mass == F(successes, len(maps))
        graph_count += 1 << variables
    print(f'Partite overlap moments: {moment_checks} exact checks. Product-uniform successful '
          f'block sampler: all {graph_count} finite partite hosts passed.')


def check_cube_geometry_and_janson_budget():
    sets = 0
    for k in range(1, 5):
        b = 1 << k
        es = cube_edges(k)
        hist = Counter()
        adj = [0] * b
        for a, c in es:
            adj[a] |= 1 << c
            adj[c] |= 1 << a
        connected = Counter()
        for mask in range(1, 1 << b):
            s = mask.bit_count()
            e = sum((mask >> a & 1) and (mask >> c & 1) for a, c in es)
            assert (1 << (2 * e)) <= s ** s
            hist[(s, e)] += 1
            seen = mask & -mask
            frontier = seen
            while frontier:
                u = (frontier & -frontier).bit_length() - 1
                frontier &= frontier - 1
                new = adj[u] & mask & ~seen
                seen |= new
                frontier |= new
            if seen == mask:
                connected[s] += 1
            sets += 1
        for s, c in connected.items():
            assert c <= b * (4 * k) ** (s - 1)
        ell = 64 * b
        overlap_sum = sum(F(c * (1 << e), ell ** s)
                          for (s, e), c in hist.items() if e)
        assert overlap_sum <= F(32 * k * b, ell * ell)
    for k in range(1, 1001):
        # Logarithmic check of the all-k ratio estimate; no huge cube allocated.
        assert 2 * log2(k) <= k + 1 + 1e-12
        ratio_log = log2(4 * sqrt(exp(1)) / 64) + log2(k) - k / 2
        assert ratio_log < -2
    print(f'Cube isoperimetry, connected-support bounds, and Janson overlap budget: '
          f'{sets} source subsets and 1000 parameter checks passed.')


def check_star_geometry():
    total_marks = 0
    total_supports = 0
    for t in range(2, 6):
        ev = [x for x in range(1 << t) if x.bit_count() % 2 == 0]
        odd = [x for x in range(1 << t) if x.bit_count() % 2]
        idx = {x: i for i, x in enumerate(ev)}
        nb = [sum(1 << idx[y ^ (1 << j)] for j in range(t)) for y in odd]
        m = len(odd)
        conflict = [sum(1 << j for j in range(m) if i != j and nb[i] & nb[j])
                    for i in range(m)]
        dist = Counter()
        for marks in range(1 << len(ev)):
            z = sum(marks & nn == nn for nn in nb)
            dist[z] += 1
        denom = 1 << len(ev)
        assert sum(F(z * c, denom) for z, c in dist.items()) == F(1, 2)
        expected_binom = [F(0) for _ in range(m + 1)]
        connected_counts = Counter()
        for mask in range(1 << m):
            s = mask.bit_count()
            union = 0
            for i in range(m):
                if mask >> i & 1:
                    union |= nb[i]
            expected_binom[s] += F(1, 1 << union.bit_count())
            assert union.bit_count() >= t * s - s * (s - 1)
            # Exact factorization over distance-two components.
            todo = mask
            unions = []
            components = 0
            while todo:
                seen = todo & -todo
                frontier = seen
                while frontier:
                    j = (frontier & -frontier).bit_length() - 1
                    frontier &= frontier - 1
                    new = conflict[j] & todo & ~seen
                    seen |= new
                    frontier |= new
                un = 0
                for j in range(m):
                    if seen >> j & 1:
                        un |= nb[j]
                assert all(not (un & old) for old in unions)
                unions.append(un)
                todo &= ~seen
                components += 1
            if components == 1:
                connected_counts[s] += 1
            total_supports += 1
        for s in range(m + 1):
            direct = sum(F(comb(z, s) * c, denom) for z, c in dist.items() if z >= s)
            assert direct == expected_binom[s]
        for s, c in connected_counts.items():
            assert c <= m * (4 * comb(t, 2)) ** (s - 1)
        total_marks += denom
    print(f'Outer-cube star moments and exact component factorization: '
          f'{total_marks} marking patterns and {total_supports} supports passed.')


def check_query_overlap_count():
    checks = 0
    for t, k, C in [(3, 1, 2), (4, 1, 3), (4, 2, 2), (5, 2, 2), (5, 3, 1)]:
        b, h = 1 << k, 1 << (t + k)
        n = C * h
        odd = [x for x in range(1 << t) if x.bit_count() % 2]
        es = cube_edges(k)
        oriented = es + [(c, a) for a, c in es]
        total = F(0)
        for y, z in combinations(odd, 2):
            shared = 2 if (y ^ z).bit_count() == 2 else 0
            for a, aa in oriented:
                for c, cc in oriented:
                    variables = 4 * t - (shared if a == c else 0) - (shared if aa == cc else 0)
                    total += F(comb(n, 2), 1 << variables)
        assert total <= C * C * k * k * b ** 4
        checks += 1
    print(f'Actual outer-neighborhood query-overlap union bound: {checks} exact cases passed.')


def check_capacity():
    m, b, D, L = 32, 4, 4, 80
    rows = m * b
    width = L // D
    n = rows * width
    lists = [set((i * width + j) % n for j in range(L)) for i in range(rows)]
    blocks = [[y + a * m for a in range(b)] for y in range(m)]
    load = Counter(v for S in lists for v in S)
    assert min(load.values()) == max(load.values()) == D
    for block in blocks:
        assert sum(len(lists[i]) for i in block) == len(set().union(*(lists[i] for i in block)))
    for S in lists:
        assert sum(len(S & T) for T in lists) == D * L
    failures = 0
    trials = 500
    for _ in range(trials):
        used = set()
        for block in blocks:
            parts = [sorted(lists[i] - used)[:L // 2] for i in block]
            if any(len(P) < L // 2 for P in parts):
                failures += 1
                break
            chosen = [rng.choice(P) for P in parts]
            assert len(set(chosen)) == b
            assert not used.intersection(chosen)
            used.update(chosen)
        else:
            assert len(used) == rows
    bound = rows * (4 * exp(1) * D / L) ** (L / 2)
    print(f'Stopped greedy capacity audit: exact column/overlap budgets; {trials} trials, '
          f'{failures} failures, single-trial proved bound {bound:.3g}.')


def check_end_to_end_blocks():
    """Finite actual-host certificates, not tests at the asymptotic thresholds.

    To exercise both reservoirs, two query-overlapping blocks are deliberately
    selected. In the small reserve we additionally delete every vertex in two
    reserve lists. On the theorem's no-overlap event this extra pruning is void.
    """
    def set_bits(mask):
        answer = []
        while mask:
            bit = mask & -mask
            answer.append(bit.bit_length() - 1)
            mask ^= bit
        return answer

    reports = []
    for d, k, n in [(6, 2, 8192), (7, 2, 16384), (6, 3, 8192)]:
        b, t, h = 1 << k, d - k, 1 << d
        ev = [x for x in range(1 << t) if x.bit_count() % 2 == 0]
        odd = [x for x in range(1 << t) if x.bit_count() % 2]
        m = len(ev)
        es = cube_edges(k)
        ell = 8 if k == 2 else 4
        L = 2 * ell
        f = {(x, a): i * b + a for i, x in enumerate(ev) for a in range(b)}
        planted = {tuple(sorted((f[x, a], f[x, c]))) for x in ev for a, c in es}
        total_A = m * b
        certificate = None
        for attempt in range(1, 101):
            local = random.Random(SEED + 100000 * d + 1000 * k + attempt)
            cross = [[local.getrandbits(n) for _ in range(total_A)] for _ in range(2)]
            offsets = [total_A, total_A + n]
            all_bits = (1 << n) - 1

            def raw_lists(reservoir, ys):
                result = {}
                for y in ys:
                    for a in range(b):
                        mask = all_bits
                        for j in range(t):
                            mask &= cross[reservoir][f[y ^ (1 << j), a]]
                        result[y, a] = mask
                return result

            raw = raw_lists(0, odd)
            exclusive = {}
            for y in odd:
                repeated = seen = 0
                for a in range(b):
                    repeated |= seen & raw[y, a]
                    seen |= raw[y, a]
                for a in range(b):
                    exclusive[y, a] = set(set_bits(raw[y, a] & ~repeated))
            if any(len(S) < L for S in exclusive.values()):
                continue
            lists = {r: set(local.sample(sorted(S), L)) for r, S in exclusive.items()}
            # Force a genuine shared potential internal edge for the reserve test.
            y0, y1 = odd[:2]
            common0 = exclusive[y0, 0] & exclusive[y1, 0]
            common1 = exclusive[y0, 1] & exclusive[y1, 1]
            if not common0 or not common1:
                continue
            for a, shared in [(0, min(common0)), (1, min(common1))]:
                for y in [y0, y1]:
                    lists[y, a] = {shared} | set(local.sample(
                        sorted(exclusive[y, a] - {shared}), L - 1))
            query_sets = {}
            owner = {}
            dirty = set()
            for y in odd:
                queries = {tuple(sorted((u, v))) for a, c in es
                           for u in lists[y, a] for v in lists[y, c]}
                query_sets[y] = queries
                for edge in queries:
                    if edge in owner:
                        dirty.update([y, owner[edge]])
                    else:
                        owner[edge] = y
            assert y0 in dirty and y1 in dirty
            clean = [y for y in odd if y not in dirty]
            seen_queries = set()
            for y in clean:
                assert seen_queries.isdisjoint(query_sets[y])
                seen_queries.update(query_sets[y])
            caches = [{}, {}]

            def edge_in_reservoir(i, u, v):
                assert u != v
                key = tuple(sorted((u, v)))
                if key not in caches[i]:
                    caches[i][key] = local.randrange(2)
                return caches[i][key]

            def sample_cube(i, parts):
                # Reveal only this block's possible required edges.
                for a, c in es:
                    for u in parts[a]:
                        for v in parts[c]:
                            edge_in_reservoir(i, u, v)
                good = [g for g in product(*parts)
                        if all(edge_in_reservoir(i, g[a], g[c]) for a, c in es)]
                mu = F(ell ** b, 1 << len(es))
                if len(good) < mu / 2:
                    return None
                return local.choice(good)

            embedding = {x * b + a: f[x, a] for x in ev for a in range(b)}
            used = set()
            failed = False
            for y in clean:
                if any(len(lists[y, a] - used) < ell for a in range(b)):
                    failed = True
                    break
                parts = [local.sample(sorted(lists[y, a] - used), ell) for a in range(b)]
                assert set(caches[0]).isdisjoint(query_sets[y])
                g = sample_cube(0, parts)
                if g is None:
                    failed = True
                    break
                assert len(set(g)) == b and used.isdisjoint(g)
                used.update(g)
                embedding.update({y * b + a: offsets[0] + g[a] for a in range(b)})
            if failed:
                continue
            reserve = raw_lists(1, sorted(dirty))
            repeated = seen = 0
            for mask in reserve.values():
                repeated |= seen & mask
                seen |= mask
            reserve = {r: set_bits(mask & ~repeated) for r, mask in reserve.items()}
            if any(len(S) < ell for S in reserve.values()):
                continue
            for y in sorted(dirty):
                parts = [local.sample(reserve[y, a], ell) for a in range(b)]
                g = sample_cube(1, parts)
                if g is None:
                    failed = True
                    break
                embedding.update({y * b + a: offsets[1] + g[a] for a in range(b)})
            if failed:
                continue
            assert len(embedding) == h and len(set(embedding.values())) == h

            def host_edge(u, v):
                if u > v:
                    u, v = v, u
                if v < total_A:
                    return (u, v) in planted
                if u < total_A:
                    i = 0 if v < offsets[1] else 1
                    return bool(cross[i][u] >> (v - offsets[i]) & 1)
                i = 0 if u < offsets[1] else 1
                assert (v < offsets[1]) == (i == 0)
                key = (u - offsets[i], v - offsets[i])
                assert key in caches[i]
                return bool(caches[i][key])

            for u, v in cube_edges(d):
                assert host_edge(embedding[u], embedding[v])
            squares = 0
            for u in range(h):
                for i, j in combinations(range(d), 2):
                    if u >> i & 1 or u >> j & 1:
                        continue
                    cycle = [u, u ^ (1 << i), u ^ (1 << i) ^ (1 << j), u ^ (1 << j)]
                    assert len({embedding[x] for x in cycle}) == 4
                    assert all(host_edge(embedding[cycle[a]], embedding[cycle[(a + 1) % 4]])
                               for a in range(4))
                    squares += 1
            certificate = (d, k, len(clean), len(dirty), len(cube_edges(d)), squares, attempt)
            break
        assert certificate is not None
        reports.append(certificate)
    for d, k, clean, dirty, edges, squares, attempt in reports:
        print(f'Actual-host completion certificate Q_{d}, blocks Q_{k}: {clean} clean / '
              f'{dirty} reserved blocks, {edges} edges and {squares} commuting squares '
              f'verified (finite diagnostic instance, attempt {attempt}).')


def check_spectral_preparation():
    checks = 0
    for N in [32, 48, 64]:
        es = [e for e in combinations(range(N), 2) if rng.random() < .65]
        A = np.array(adjacency(N, es), dtype=float)
        p = 2 * len(es) / (N * (N - 1))
        assert p >= .5
        B = A - p * (np.ones((N, N)) - np.eye(N))
        op = max(abs(np.linalg.eigvalsh(B)))
        K2 = op * op / N
        for _ in range(30):
            k = rng.randrange(1, min(4, N // 8) + 1)
            gamma = (1 - 1 / (2 * k)) / 2
            size = rng.randrange(8 * k, N + 1)
            T = rng.sample(range(N), size)
            degrees = A[:, T].sum(axis=1)
            bad = degrees < gamma * size
            deviations = B[:, T].sum(axis=1)
            assert np.all(deviations[bad] <= -size / (8 * k) + 1e-10)
            assert deviations @ deviations <= K2 * N * size + 1e-7
            assert bad.sum() <= 64 * K2 * k * k * N / size + 1e-8
            checks += 1
    budgets = 0
    for k in range(1, 41):
        b = 1 << k
        gamma = F(2 * k - 1, 4 * k)
        assert gamma ** k >= F(1, 2 * b)
        for K2, sigma in product([F(0), F(1, 4), F(1), F(100)],
                                  [F(1), F(1, 2), F(1, 16), F(1, 1000)]):
            N = ceil(4096 * (K2 + 1) * (k + 1) ** 3 * b ** 2 / sigma ** 2)
            a0 = sigma * N / (4 * b)
            assert sigma * N * gamma ** k - b >= a0
            assert a0 >= 8 * k
            loss = b + 256 * K2 * k ** 3 * b / sigma
            assert loss <= a0
            for r in range(k + 1):
                choices = sigma * N * gamma ** r - loss
                assert choices >= sigma * N * gamma ** r / 2
                assert choices >= sigma * N / (4 * b)
            budgets += 1
    print(f'Spectral preparation: {checks} matrix/set checks and {budgets} exact rational '
          f'greedy-count/spread-budget checks passed.')


def check_large_parameters():
    mp.mp.dps = 100
    ln2 = mp.log(2)
    C = 1 << 14
    ds = sorted(set([1 << 16, (1 << 16) + 1, 10**6]
                    + [2 ** j + delta for j in range(17, 129) for delta in [-1, 0, 1]]
                    + [rng.randrange(1 << 16, 10**12) for _ in range(150)]))
    for d in ds:
        dmp = mp.mpf(d)
        ld = mp.log(dmp, 2)
        k = int(mp.ceil(mp.log(dmp * ld, 2)))
        b = 1 << k
        # Correct a possible tiny roundoff at exact powers of two.
        if k and mp.mpf(b // 2) >= dmp * ld:
            k -= 1
            b //= 2
        t = d - k
        L, ell = C * b // 4, C * b // 8
        assert mp.mpf(b) >= dmp * ld
        assert b <= d * d and k <= 2 * ld
        assert 2 * t >= d and t >= 1 << 15
        assert mp.mpf(b) / k >= dmp / 2
        assert 2 * k < d - 1
        r = int(mp.ceil(3 * mp.mpf(t) / mp.log(t, 2)))
        assert 4 * r <= t
        theta_r2_log = 1 + 2 * mp.log(t, 2) - 3 * mp.mpf(t) / 4 + 2 * mp.log(r, 2)
        assert theta_r2_log <= -1
        star_tail_log = (mp.mpf(r) / 2 + mp.mpf('.5')) / ln2 - r * mp.log(r, 2)
        assert star_tail_log <= -2 * t
        logs = [
            (d - 1) * ln2 - C * b / 16,
            mp.log(C) + mp.log(b) + (d - 2 * t) * ln2,
            mp.log(C) + d * ln2 - 2 * b,
            mp.log(2) + 2 * mp.log(C) + 2 * mp.log(k) + 4 * mp.log(b) - dmp * ln2 / 4,
            (d - 1) * ln2 - L * ln2,
            d * ln2 - mp.mpf(ell) ** 2 / (512 * k * b),
            mp.log(2) + mp.log(C) + 4 * mp.log(b) - dmp * ln2 / 2,
            (d - 1) * ln2 - C * b / 8,
        ]
        top = max(logs)
        total_log = top + mp.log(sum(mp.exp(z - top) for z in logs))
        assert total_log <= (32 + 10 * ld - dmp / 4) * ln2
        assert 32 + 10 * ld <= dmp / 8
        assert total_log <= -dmp * ln2 / 8
        # Packing bound checked after taking a logarithm of its enormous negative term.
        rhs = (k + 1 + mp.mpf(1) / 8) * dmp * ln2 + mp.log(k + 1)
        assert dmp - 5 - k >= mp.log(rhs, 2)
    print(f'Large-parameter audit: {len(ds)} dimensions from 2^16 through 2^128+1; '
          f'column truncation, Janson, total error, and initial packing budgets passed.')


def main():
    assert hashlib.sha256((ROOT / 'Spec.lean').read_bytes()).hexdigest() == SPEC_HASH
    print('Cube block amplification verification; deterministic seed', SEED)
    check_block_lifts()
    check_gram()
    check_collision_formula()
    check_partite_moments_and_sampler()
    check_cube_geometry_and_janson_budget()
    check_star_geometry()
    check_query_overlap_count()
    check_capacity()
    check_end_to_end_blocks()
    check_spectral_preparation()
    check_large_parameters()
    assert hashlib.sha256((ROOT / 'Spec.lean').read_bytes()).hexdigest() == SPEC_HASH
    print('All checks passed. Spec.lean SHA-256 unchanged:', SPEC_HASH)
    print('Scope: finite identity/constant checks only; no proof of the uniform spectral or Ramsey benchmark.')


if __name__ == '__main__':
    main()
