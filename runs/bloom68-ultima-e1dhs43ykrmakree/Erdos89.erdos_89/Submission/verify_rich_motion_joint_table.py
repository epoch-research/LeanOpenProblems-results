#!/usr/bin/env python3
"""Exact checks for rich_motion_joint_table.md.

The asymptotic coloring is established by the probability proof, not by tests
at tiny parameters. The finite constructed tables below test its algebraic
identities and the edge-correspondence lift. No planar realization of those
abstract tables is claimed.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, e, fsum, isqrt, log
import random

import networkx as nx


RNG = random.Random(9462307)


def strata(t):
    assert t >= 2 and t & (t - 1) == 0
    n = 1 << t
    D = n // t
    r = t * (n - 1)
    levels = []
    for j in range(1, t // 2 + 1):
        k = 1 << j
        multiplicity = 2 * ((n - 2) // (k * (k - 1)))
        assert multiplicity % 2 == 0 and multiplicity > 0
        assert n - 2 <= multiplicity * k * (k - 1) <= 2 * (n - 2)
        levels.append((j, k, multiplicity))
    filler = r - 1 - sum(m * k * (k - 1) for _, k, m in levels)
    assert 0 < filler < 3 * n and filler % 2 == 1
    assert 1 + sum(m * k * (k - 1) for _, k, m in levels) + filler == r
    counts = Counter({n: 1})
    for _, k, m in levels:
        counts[k] += m * n * (n - 1)
    counts[2] += filler * comb(n, 2)
    running = 0
    max_tail = F(0)
    for k in sorted(counts, reverse=True):
        running += counts[k]
        ratio = F(running * k * k, n ** 3)
        assert ratio <= 12
        max_tail = max(max_tail, ratio)
    energy = sum(count * k * (k - 1) for k, count in counts.items())
    assert energy == D * r * r == t * n * (n - 1) ** 2
    assert energy * D == (n * (n - 1)) ** 2
    assert F(energy * D * D, n ** 5) == F((n - 1) ** 2, t * n * n)
    return n, D, r, levels, filler, counts, max_tail


def check_asymptotic_parameters():
    for t in (2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048):
        n, D, r, levels, filler, counts, tail = strata(t)
        if t >= 64:
            assert D >= 1 << 58
            assert n <= D * D
            assert t ** 8 <= n
            assert t ** 3 <= isqrt(n)
            # Stronger elementary versions of the numerical union-bound tests.
            assert isqrt(D) - 1 >= 33 * t
            # Since log(D)<t, this implies D^2 exp(-D/32)<exp(-10).
            assert D // 32 > 2 * t + 10
            assert F(5 * t * t, 9) > 1
        print(f"Strata: t={t}, L={len(levels)}, max tail ratio={float(tail):.6f}")
    assert log(4 / 3) > 1 / 4
    assert 4 * (e / 8) ** 8 < 1 / 2
    for k in range(17, 200):
        assert F(33 * k, 16) - F(k * (k - 1), 4) <= -k
    print("Asymptotic integer parameters and probability-bound constants: PASS")


def gf_mul(a, b, t, modulus):
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & (1 << t):
            a ^= modulus
    return result


def abstract_model(t):
    n, D, r, levels, filler, _, _ = strata(t)
    modulus = {2: 0b111, 4: 0b10011}[t]
    vertices = tuple(range(n))
    all_edges = list(combinations(vertices, 2))
    shuffled = all_edges[:]
    RNG.shuffle(shuffled)
    colors = {edge: i // (r // 2) for i, edge in enumerate(shuffled)}
    assert Counter(colors.values()) == Counter({d: r // 2 for d in range(D)})

    domains = [frozenset(vertices)]
    inverse = {0: 0}
    for _, k, copies in levels:
        S = tuple(range(k))
        family = []
        cover = Counter()
        for a in range(1, n):
            for b in range(n):
                Q = frozenset(gf_mul(a, x, t, modulus) ^ b for x in S)
                assert len(Q) == k
                family.append(Q)
                cover.update(combinations(sorted(Q), 2))
        assert len(family) == n * (n - 1)
        assert all(cover[edge] == k * (k - 1) for edge in all_edges)
        for _ in range(copies // 2):
            first = len(domains)
            domains.extend(family)
            second = len(domains)
            domains.extend(family)
            for offset in range(len(family)):
                inverse[first + offset] = second + offset
                inverse[second + offset] = first + offset

    pairs = [frozenset(edge) for edge in all_edges]
    first = len(domains)
    domains.extend(pairs)
    for offset in range(len(pairs)):
        inverse[first + offset] = first + offset
    for _ in range((filler - 1) // 2):
        first = len(domains)
        domains.extend(pairs)
        second = len(domains)
        domains.extend(pairs)
        for offset in range(len(pairs)):
            inverse[first + offset] = second + offset
            inverse[second + offset] = first + offset

    incidence = {edge: [] for edge in all_edges}
    table = []
    for g, Q in enumerate(domains):
        row = Counter()
        for edge in combinations(sorted(Q), 2):
            incidence[edge].append(g)
            row[colors[edge]] += 2
        assert sum(row.values()) == len(Q) * (len(Q) - 1)
        assert all(0 < a <= r and a % 2 == 0 for a in row.values())
        table.append(row)
    assert all(len(gs) == r for gs in incidence.values())
    assert all(sum(row[d] for row in table) == r * r for d in range(D))
    assert table[0] == Counter({d: r for d in range(D)})
    assert all(inverse[inverse[g]] == g for g in range(len(domains)))
    assert all(domains[g] == domains[inverse[g]] for g in range(len(domains)))
    assert all(table[g] == table[inverse[g]] for g in range(len(domains)))
    assert sum(inverse[g] == g for g in inverse) == comb(n, 2) + 1
    for k in sorted({len(Q) for Q in domains}):
        rich = sum(len(Q) >= k for Q in domains)
        assert rich * k * k <= 12 * n ** 3

    def induced_counts(Q):
        row = Counter()
        for edge in combinations(sorted(Q), 2):
            row[colors[edge]] += 2
        return row

    if n == 4:
        # Exhaustive tuple identities through order three.
        for order in (1, 2, 3):
            totals = Counter()
            for gs in product(range(len(domains)), repeat=order):
                Q = frozenset.intersection(*(domains[g] for g in gs))
                b = induced_counts(Q)
                assert sum(b.values()) == len(Q) * (len(Q) - 1)
                totals.update(b)
            assert totals == Counter({d: r ** (order + 1) for d in range(D)})
    for _ in range(40):
        chosen = RNG.sample(range(len(domains)), 2)
        Q = domains[chosen[0]] & domains[chosen[1]]
        b = induced_counts(Q)
        totals = Counter()
        for R in domains:
            totals.update(induced_counts(Q & R))
        assert totals == Counter({d: r * value for d, value in b.items()})

    # Exact weighted Gram/domain inequality, including signed coefficients.
    for _ in range(20):
        chosen = RNG.sample(range(len(domains)), min(25, len(domains)))
        z = {g: RNG.randrange(-4, 5) for g in chosen}
        for d in range(D):
            lhs = 0
            for edge, memberships in incidence.items():
                if colors[edge] == d:
                    total = sum(z.get(g, 0) for g in memberships)
                    lhs += 2 * total * total
            linear = sum(z[g] * table[g][d] for g in chosen)
            assert r * lhs >= linear * linear
    print(f"Abstract domains: n={n}, D={D}, r={r}, rows={len(domains)}: PASS")
    return n, D, r, colors, domains, table, incidence


def edge_correspondence_lift(model):
    n, D, r, colors, domains, table, incidence = model
    R = r // 2
    row_maps = [dict() for _ in domains]
    for d in range(D):
        source_edges = sorted(edge for edge in colors if colors[edge] == d)
        assert len(source_edges) == R
        active_rows = sorted({g for edge in source_edges for g in incidence[edge]})
        right_index = {g: j for j, g in enumerate(active_rows)}
        N = max(2 * R, len(active_rows))
        multiplicity = Counter()
        original = {}
        left_degree = [0] * N
        right_degree = [0] * N
        for i, edge in enumerate(source_edges):
            gs = incidence[edge]
            assert len(gs) == 2 * R
            for j, g in enumerate(gs):
                u = 2 * i + (j // R)
                v = right_index[g]
                key = (u, v)
                assert key not in original
                original[key] = (g, edge)
                multiplicity[key] += 1
                left_degree[u] += 1
                right_degree[v] += 1
        assert max(left_degree) <= R and max(right_degree) <= R
        # Make an R-regular bipartite multigraph, keeping multiplicities exact.
        ld = [R - degree for degree in left_degree]
        rd = [R - degree for degree in right_degree]
        i = j = 0
        while i < N and j < N:
            if ld[i] == 0:
                i += 1
                continue
            if rd[j] == 0:
                j += 1
                continue
            amount = min(ld[i], rd[j])
            multiplicity[i, j] += amount
            ld[i] -= amount
            rd[j] -= amount
        assert not any(ld) and not any(rd)
        graph = nx.Graph()
        graph.add_nodes_from(range(2 * N))
        graph.add_edges_from((u, N + v) for u, v in multiplicity)
        assigned = {}
        for edge_color in range(R):
            matching = nx.algorithms.bipartite.hopcroft_karp_matching(
                graph, top_nodes=range(N))
            assert len(matching) == 2 * N
            for u in range(N):
                v = matching[u] - N
                key = (u, v)
                if key in original:
                    g, edge = original.pop(key)
                    assigned[g, edge] = edge_color
                multiplicity[key] -= 1
                if multiplicity[key] == 0:
                    graph.remove_edge(u, N + v)
        assert not original and all(count == 0 for count in multiplicity.values())
        target_for_color = {assigned[0, edge]: edge for edge in source_edges}
        assert len(target_for_color) == R
        by_source_target = defaultdict(list)
        for (g, edge), edge_color in assigned.items():
            target = target_for_color[edge_color]
            by_source_target[edge, target].append(g)
        assert len(by_source_target) == R * R
        for (edge, target), gs in by_source_target.items():
            assert len(gs) == 2
            gs.sort()
            if 0 in gs:
                assert edge == target and gs[0] == 0
            for orientation, g in enumerate(gs):
                row_maps[g][edge] = (target, orientation)

    records = []
    unique = {}
    for g, row_map in enumerate(row_maps):
        expected = set(combinations(sorted(domains[g]), 2))
        assert set(row_map) == expected
        assert len({target for target, bit in row_map.values()}) == len(expected)
        for source, (target, bit) in row_map.items():
            assert colors[source] == colors[target]
            if g == 0:
                assert source == target and bit == 0
            for source_orientation in (0, 1):
                B = source if source_orientation == 0 else source[::-1]
                target_orientation = bit ^ source_orientation
                image = target if target_orientation == 0 else target[::-1]
                key = (B, image)
                assert key not in unique
                unique[key] = g
                records.append((B, g, image[0], image[1]))
    assert len(unique) == D * r * r
    for d in range(D):
        directed = [v for edge in colors if colors[edge] == d
                    for v in (edge, edge[::-1])]
        assert all((source, target) in unique for source in directed for target in directed)

    def entropy(indices, weights):
        masses = Counter()
        for rec, w in zip(records, weights):
            masses[tuple(rec[i] for i in indices)] += w
        total = sum(weights)
        return -fsum((v / total) * log(v / total) for v in masses.values())

    for weights in ([1] * len(records),
                    [RNG.randrange(1, 101) for _ in records]):
        HB = entropy((0,), weights)
        HBG = entropy((0, 1), weights)
        HBX = entropy((0, 2), weights)
        HBY = entropy((0, 3), weights)
        HBXY = entropy((0, 2, 3), weights)
        HBGX = entropy((0, 1, 2), weights)
        HBGY = entropy((0, 1, 3), weights)
        deficit = (HBG - HB) - (HBGX - HBX) - (HBGY - HBY)
        mutual = HBX + HBY - HB - HBXY
        assert abs(HBG - HBXY) < 1e-10
        assert abs(deficit - mutual) < 1e-10 and deficit >= -1e-10
    print(f"Edge lift and arbitrary-weight entropy: n={n}, quadruples={len(records)}: PASS")


# Exact rational plane geometry.
def add(p, q):
    return p[0] + q[0], p[1] + q[1]


def neg(p):
    return -p[0], -p[1]


def sub(p, q):
    return add(p, neg(q))


def cmul(p, q):
    return p[0] * q[0] - p[1] * q[1], p[0] * q[1] + p[1] * q[0]


def norm2(p):
    return p[0] ** 2 + p[1] ** 2


def act(g, p):
    return add(cmul(g[:2], p), g[2:])


def compose(h, g):
    # h after g
    a = cmul(h[:2], g[:2])
    b = add(cmul(h[:2], g[2:]), h[2:])
    return a + b


def inverse_motion(g):
    a = (g[0], -g[1])
    b = neg(cmul(a, g[2:]))
    return a + b


def edge_motion(source, target):
    p, q = source
    x, y = target
    v, w = sub(q, p), sub(y, x)
    den = norm2(v)
    a = (F(w[0] * v[0] + w[1] * v[1], den),
         F(w[1] * v[0] - w[0] * v[1], den))
    assert norm2(a) == 1
    return a + sub(x, cmul(a, p))


def geometric_checks():
    P = frozenset(product(range(3), range(2)))
    E = defaultdict(set)
    for p in P:
        for q in P:
            if p != q:
                E[norm2(sub(p, q))].add((p, q))
    motions = set()
    for edges in E.values():
        motions.update(edge_motion(source, target) for source in edges for target in edges)
    motions = sorted(motions)
    domains = {g: frozenset(p for p in P if act(g, p) in P) for g in motions}

    def counts(Q):
        return Counter({d: sum(p in Q and q in Q for p, q in edges)
                        for d, edges in E.items()})

    a = {g: counts(domains[g]) for g in motions}
    for d, edges in E.items():
        assert sum(a[g][d] for g in motions) == len(edges) ** 2
        for edge in edges:
            assert sum(all(p in domains[g] for p in edge) for g in motions) == len(edges)
    for g in motions:
        assert sum(a[g].values()) == len(domains[g]) * (len(domains[g]) - 1)
        assert a[g] == a[inverse_motion(g)]

    chosen = RNG.sample(motions, min(14, len(motions)))
    C, B = {}, {}
    for d, edges in E.items():
        universe = set()
        for g in chosen:
            inv = inverse_motion(g)
            universe.update((act(inv, p), act(inv, q)) for p, q in edges)
        for g in chosen:
            for h in chosen:
                u = compose(h, inverse_motion(g))
                Q_u = frozenset(p for p in P if act(u, p) in P)
                C[d, g, h] = counts(Q_u)[d]
                B[d, g, h] = counts(domains[g] & domains[h])[d]
                gram_all = gram_inside = gram_outside = 0
                for edge in universe:
                    contributes = ((act(g, edge[0]), act(g, edge[1])) in edges
                                   and (act(h, edge[0]), act(h, edge[1])) in edges)
                    if contributes:
                        gram_all += 1
                        if edge in edges:
                            gram_inside += 1
                        else:
                            gram_outside += 1
                assert C[d, g, h] == gram_all
                assert B[d, g, h] == gram_inside
                assert C[d, g, h] - B[d, g, h] == gram_outside
    W_id = sum(F(1, len(edges)) for edges in E.values())
    for _ in range(40):
        z = {g: RNG.randrange(-5, 6) for g in chosen}
        left = sum(F(z[g] * z[h] * C[d, g, h], len(edges) ** 2)
                   for d, edges in E.items() for g in chosen for h in chosen)
        middle = sum(F(sum(z[g] * a[g][d] for g in chosen) ** 2, len(edges) ** 3)
                     for d, edges in E.items())
        linear = sum(F(z[g] * a[g][d], len(edges) ** 2)
                     for d, edges in E.items() for g in chosen)
        assert left >= middle >= linear * linear / W_id
    print(f"Actual planar Gram domination: n={len(P)}, motions={len(motions)}: PASS")


def kernel_checks():
    for L in (1, 2, 4, 8, 12):
        N = 1 << L
        W = {}
        for u in range(-N + 1, N):
            W[u] = sum(F(max((1 << j) - abs(u), 0), 1 << (2 * j))
                       for j in range(1, L + 1))
        assert sum(W.values()) == L
        assert F(1, 2) <= W[0] < 1
        for u, value in W.items():
            if u:
                assert value <= F(2, abs(u))
        value_counts = Counter(W.values())
        count = 0
        weak = F(0)
        for value in sorted(value_counts, reverse=True):
            count += value_counts[value]
            weak = max(weak, value * count)
        assert weak <= 5
        print(f"Dyadic correlation kernel: L={L}, L1={sum(W.values())}, weak={float(weak):.6f}: PASS")


def vadd(a, b):
    return tuple(x + y for x, y in zip(a, b))


def vneg(a):
    return tuple(-x for x in a)


def rich_group_checks():
    # Formal Q-independent coordinates; they can be evaluated at independent
    # real generators without changing any equalities checked here.
    for q in (4, 5, 6, 8):
        s = q + 1
        m = 2 * s
        dimension = s + q
        basis = [tuple(int(i == j) for j in range(dimension)) for i in range(dimension)]
        A = [v for a in basis[:s] for v in (a, vneg(a))]
        B = basis[s:]
        P = {vadd(a, b) for a in A for b in B}
        assert len(P) == m * q
        differences, sums = Counter(), Counter()
        for x in P:
            for y in P:
                differences[vadd(y, vneg(x))] += 1
                sums[vadd(y, x)] += 1
        T = {vadd(b, vneg(c)) for b in B for c in B}
        H = {vadd(b, c) for b in B for c in B}
        assert {u for u, k in differences.items() if k >= m} == T
        assert {c for c, k in sums.items() if k >= m} == H
        motions = {(1, u) for u in T} | {(-1, c) for c in H}
        expected = q * (q - 1) + 1 + comb(q + 1, 2)
        assert len(motions) == expected
        products = set()
        for sign1, c1 in motions:
            for sign2, c2 in motions:
                products.add((sign1 * sign2, vadd(c1, c2 if sign1 == 1 else vneg(c2))))
        disjoint_products = set()
        for plus in combinations(range(q), 2):
            for minus in combinations([i for i in range(q) if i not in plus], 2):
                value = vadd(vadd(B[plus[0]], B[plus[1]]),
                             vneg(vadd(B[minus[0]], B[minus[1]])))
                disjoint_products.add(value)
        assert len(disjoint_products) == comb(q, 2) * comb(q - 2, 2)
        assert all((1, value) in products for value in disjoint_products)
        print(f"Full rich set: q={q}, n={len(P)}, k={m}, |G|={len(motions)}, "
              f"|G^2|={len(products)}, doubling={len(products)/len(motions):.3f}: PASS")


if __name__ == '__main__':
    check_asymptotic_parameters()
    for t in (2, 4):
        model = abstract_model(t)
        edge_correspondence_lift(model)
    geometric_checks()
    kernel_checks()
    rich_group_checks()
    print("ALL CHECKS PASSED. The sharp planar conjecture is not proved.")
