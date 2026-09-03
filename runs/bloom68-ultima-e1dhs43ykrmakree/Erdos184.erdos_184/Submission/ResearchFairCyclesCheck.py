#!/usr/bin/env python3
"""Exact finite checks for ResearchFairCycles.md; NOT a proof of W(c).

Python 3 + NetworkX.  All weights and optimization comparisons are exact.
The infinite-family proofs are in the note.  No preexisting file is modified.
"""
from collections import Counter, defaultdict, deque
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from math import gcd
from pathlib import Path
import hashlib
import json
import random

import networkx as nx

SPEC_SHA256 = "429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde"


def edge(u, v):
    assert u != v
    return (u, v) if u < v else (v, u)


def path_edges(P):
    return [edge(u, v) for u, v in zip(P, P[1:])]


def cycle_edges(C):
    return path_edges(tuple(C) + (C[0],))


def original_weights(G):
    return {v: Fraction(1, G.degree(v)) for v in G if G.degree(v)}


def weight(C, lam):
    return sum((lam[v] for v in C), Fraction())


def arc_weight(P, lam):
    assert len(P) >= 2
    return (lam[P[0]] + lam[P[-1]]) / 2 + weight(P[1:-1], lam)


def graph_from_partition(D):
    G = nx.Graph()
    seen = set()
    for C in D:
        assert len(C) >= 3 and len(set(C)) == len(C)
        E = set(cycle_edges(C))
        assert len(E) == len(C) and not (E & seen)
        seen |= E
        G.add_edges_from(E)
    assert all(d % 2 == 0 for _, d in G.degree())
    return G


def verify_partition(G, D, lam=None):
    used = Counter()
    for C in D:
        assert len(C) >= 3 and len(set(C)) == len(C), C
        used.update(cycle_edges(C))
    assert used == Counter({edge(u, v): 1 for u, v in G.edges()})
    assert all(d % 2 == 0 for _, d in G.degree())
    if lam is None:
        lam = original_weights(G)
        assert sum((weight(C, lam) for C in D), Fraction()) == Fraction(
            sum(G.degree(v) > 0 for v in G), 2)
    else:
        assert sum((weight(C, lam) for C in D), Fraction()) == sum(
            (Fraction(G.degree(v), 2) * lam[v] for v in G if G.degree(v)),
            Fraction())
    return tuple(sorted(weight(C, lam) for C in D))


def all_cycles(G):
    """Each simple undirected cycle once, with integer vertex labels."""
    for root in sorted(G):
        def dfs(path, seen):
            u = path[-1]
            if len(path) >= 3 and root in G[u] and path[1] < u:
                yield tuple(path)
            for v in sorted(G[u]):
                if v > root and v not in seen:
                    yield from dfs(path + [v], seen | {v})
        yield from dfs([root], {root})


def exact_partition_count(G):
    """Independent enumeration of all unordered cycle edge partitions."""
    E = sorted(edge(u, v) for u, v in G.edges())
    ei = {e: i for i, e in enumerate(E)}
    masks = [sum(1 << ei[e] for e in cycle_edges(C)) for C in all_cycles(G)]
    byedge = [[] for _ in E]
    for mask in masks:
        bits = mask
        while bits:
            b = bits & -bits
            byedge[b.bit_length() - 1].append(mask)
            bits ^= b

    @lru_cache(None)
    def count(mask):
        if not mask:
            return 1
        k = (mask & -mask).bit_length() - 1
        return sum(count(mask ^ C) for C in byedge[k] if C & mask == C)
    return count((1 << len(E)) - 1)


def fair_optimum(G, lam=None):
    """Full lexicographic optimum, not just a bottleneck or count optimum.

    DP on remaining edge sets.  The fixed original weights make the sum
    constant on each state.  Sorted-multiset addition preserves lex order.
    """
    if not G.number_of_edges():
        return (), (), 0
    if lam is None:
        lam = original_weights(G)
    E = sorted(edge(u, v) for u, v in G.edges())
    ei = {e: i for i, e in enumerate(E)}
    C = list(all_cycles(G))
    masks = [sum(1 << ei[e] for e in cycle_edges(c)) for c in C]
    ws = [weight(c, lam) for c in C]
    den = 1
    for w in ws:
        den = den * w.denominator // gcd(den, w.denominator)
    wi = [int(w * den) for w in ws]
    byedge = [[] for _ in E]
    for i, mask in enumerate(masks):
        bits = mask
        while bits:
            b = bits & -bits
            byedge[b.bit_length() - 1].append(i)
            bits ^= b

    @lru_cache(None)
    def solve(mask):
        if not mask:
            return (), ()
        # Every exact cover contains precisely one choice through this edge.
        k = (mask & -mask).bit_length() - 1
        best = None
        for j in byedge[k]:
            if masks[j] & mask != masks[j]:
                continue
            suffix = solve(mask ^ masks[j])
            if suffix is None:
                continue
            profile = tuple(sorted(suffix[0] + (wi[j],)))
            if best is None or profile > best[0]:
                best = profile, (j,) + suffix[1]
        return best

    ans = solve((1 << len(E)) - 1)
    assert ans is not None
    D = tuple(C[j] for j in ans[1])
    profile = tuple(Fraction(w, den) for w in ans[0])
    assert verify_partition(G, D, lam) == profile
    return profile, D, solve.cache_info().currsize


def cyclic_arcs(C, common):
    indices = [i for i, v in enumerate(C) if v in common]
    return [tuple(C[(indices[j] + k) % len(C)] for k in range(
        (indices[(j + 1) % len(indices)] - indices[j]) % len(C) + 1))
        for j in range(len(indices))]


def coherent_arcs(C, D):
    common = set(C) & set(D)
    assert len(common) >= 2
    root = next(v for v in C if v in common)
    i = C.index(root)
    C = tuple(C[i:]) + tuple(C[:i])
    order = tuple(v for v in C if v in common)
    for seq in (tuple(D), tuple(reversed(D))):
        j = seq.index(root)
        seq = seq[j:] + seq[:j]
        if tuple(v for v in seq if v in common) == order:
            return cyclic_arcs(C, common), cyclic_arcs(seq, common)
    return None


def coherent_exchange(C, D, lam):
    arcs = coherent_arcs(C, D)
    assert arcs is not None
    A, B = arcs
    totals = [Fraction(), Fraction()]
    parts = [[], []]
    differences = []
    for P, Q in zip(A, B):
        a, b = arc_weight(P, lam), arc_weight(Q, lam)
        differences.append(abs(a - b))
        high, low = (P, Q) if a >= b else (Q, P)
        small = 0 if totals[0] <= totals[1] else 1
        parts[small].append(high)
        parts[1 - small].append(low)
        totals[small] += arc_weight(high, lam)
        totals[1 - small] += arc_weight(low, lam)
    R = [tuple(v for P in arcs_j for v in P[:-1]) for arcs_j in parts]
    G = graph_from_partition([C, D])
    verify_partition(G, R, lam)
    T = weight(C, lam) + weight(D, lam)
    assert sum(totals) == T
    assert min(totals) >= (T - max(differences)) / 2
    assert sorted(totals) == sorted(weight(Q, lam) for Q in R)
    return R, differences


def check_fair_necessary_conditions(G, D, lam):
    if not D:
        return 0, 0
    m = min(weight(C, lam) for C in D)
    tri_count = coherent_count = 0
    for C in D:
        if weight(C, lam) != m:
            continue
        for Q in D:
            if Q is C or Q == C:
                continue
            common = set(C) & set(Q)
            if len(common) >= 2:
                arcs = coherent_arcs(C, Q)
                if arcs is not None:
                    A, B = arcs
                    diff = max(abs(arc_weight(P, lam) - arc_weight(R, lam))
                               for P, R in zip(A, B))
                    if weight(Q, lam) > m:
                        assert diff >= weight(Q, lam) - m
                    else:
                        # With total 2m, a two-cycle replacement cannot have
                        # both weights above m.  Equal minima need a larger union.
                        replacement, _ = coherent_exchange(C, Q, lam)
                        assert verify_partition(graph_from_partition([C, Q]),
                                                replacement, lam) <= (m, m)
                    if len(common) >= 3 and weight(Q, lam) > 2 * m:
                        assert sum(arc_weight(R, lam) > arc_weight(P, lam)
                                   for P, R in zip(A, B)) == 1
                    coherent_count += 1
            if len(C) == 3:
                assert len(common) <= 2
                if len(common) == 2:
                    a, b = sorted(common)
                    c = next(v for v in C if v not in common)
                    arcs = cyclic_arcs(Q, {a, b})
                    internal = [weight(P[1:-1], lam) for P in arcs]
                    assert all(x <= lam[c] for x in internal)
                    assert weight(Q, lam) <= m + lam[c]
                    assert sum(internal) >= lam[c]
                    tri_count += 1
    return tri_count, coherent_count


def coherent_and_triangle_tests():
    rng = random.Random(42731)
    instances = assignments = classifications = 0
    large_ratio_cases = single_expanding_fair_cases = 0
    for r in range(3, 11):
        for _ in range(24):
            C, D = [], []
            nxt = r
            for i in range(r):
                na, nb = rng.randrange(4), rng.randrange(4)
                if na == nb == 0:
                    nb = 1
                A = list(range(nxt, nxt + na)); nxt += na
                B = list(range(nxt, nxt + nb)); nxt += nb
                C += [i] + A
                D += [i] + B
            lam = {v: Fraction(rng.randrange(1, 20), rng.randrange(1, 20))
                   for v in range(nxt)}
            replacement, diffs = coherent_exchange(tuple(C), tuple(D), lam)
            A, B = coherent_arcs(tuple(C), tuple(D))
            # Enumerate every cut choice for small rings, checking simplicity
            # and exact edge and weight accounting, not just the greedy choice.
            if r <= 7:
                G = graph_from_partition([C, D])
                candidates = []
                for bits in product((0, 1), repeat=r):
                    R = [tuple(v for i in range(r)
                               for v in ((A, B)[bits[i] ^ side][i])[:-1])
                         for side in (0, 1)]
                    candidates.append(verify_partition(G, R, lam))
                    assignments += 1
                lenses = [tuple(P) + tuple(reversed(Q))[1:-1]
                          for P, Q in zip(A, B)]
                lens_profile = verify_partition(G, lenses, lam)
                exact_profile, _, _ = fair_optimum(G, lam)
                assert len(list(all_cycles(G))) == 2 ** r + r
                assert exact_partition_count(G) == 2 ** (r - 1) + 1
                assert exact_profile == max(candidates)
                assert exact_profile > lens_profile
                m, M = weight(C, lam), weight(D, lam)
                if m > M:
                    m, M = M, m
                    A, B = B, A
                if M > 2 * m:
                    positives = sum(arc_weight(Q, lam) > arc_weight(P, lam)
                                    for P, Q in zip(A, B))
                    assert (exact_profile == (m, M)) == (positives == 1)
                    large_ratio_cases += 1
                    single_expanding_fair_cases += (positives == 1)
                classifications += 1
            instances += 1

    # Two shared triangle vertices: test the sharp arc condition against the
    # actual full optimum with arbitrary positive rational vertex weights.
    triangle = (0, 1, 2)
    Q = (0, 3, 1, 4)
    G = graph_from_partition([triangle, Q])
    forced_old_optima = 0
    for _ in range(120):
        lam = {v: Fraction(rng.randrange(1, 16), rng.randrange(1, 8))
               for v in G}
        profile, opt, _ = fair_optimum(G, lam)
        check_fair_necessary_conditions(G, opt, lam)
        m = weight(triangle, lam)
        if weight(Q, lam) >= m and max(lam[3], lam[4]) > lam[2]:
            x, y = (3, 4) if lam[3] >= lam[4] else (4, 3)
            R = [(0, x, 1), (0, 2, 1, y)]
            p = verify_partition(G, R, lam)
            assert p[0] > m
            assert profile > tuple(sorted((m, weight(Q, lam))))
        if tuple(sorted((m, weight(Q, lam)))) == profile:
            forced_old_optima += 1
    assert 0 < single_expanding_fair_cases < large_ratio_cases
    return dict(coherent_instances=instances, all_assignments=assignments,
                exact_coherent_classifications=classifications,
                large_ratio_cases=large_ratio_cases,
                single_expanding_fair_cases=single_expanding_fair_cases,
                triangle_weight_tests=120, old_triangle_optimal=forced_old_optima)


PAIRS = ((0, 1), (1, 2), (0, 2))


def orient_path(P, a, b):
    if (P[0], P[-1]) == (a, b):
        return tuple(P)
    assert (P[-1], P[0]) == (a, b)
    return tuple(reversed(P))


def block_paths(i, long_pair):
    a, b = long_pair
    c = next(v for v in range(3) if v not in (a, b))
    x, y = 3 + 2 * i, 4 + 2 * i
    paths = [(a, x, y, b), (b, x, c), (c, y, a)]
    return {edge(P[0], P[-1]): orient_path(P, *edge(P[0], P[-1]))
            for P in paths}


def port_cycle(P):
    paths = [orient_path(P[(0, 1)], 0, 1),
             orient_path(P[(1, 2)], 1, 2),
             orient_path(P[(0, 2)], 2, 0)]
    return tuple(v for path in paths for v in path[:-1])


def outside_count(P):
    return sum(len(path) - 2 for path in P.values())


def join_k2(k):
    G = nx.complete_graph(3)
    for i in range(k):
        x, y = 3 + 2 * i, 4 + 2 * i
        G.add_edge(x, y)
        G.add_edges_from((v, z) for v in range(3) for z in (x, y))
    return G


def join_k2_fair_partition(k):
    assert k >= 1
    if k <= 2:
        P = [{(0, 1): (0, 3, 4, 1), (1, 2): (1, 2), (0, 2): (0, 2)},
             {(0, 1): (0, 1), (1, 2): (1, 3, 2), (0, 2): (0, 4, 2)}]
        if k == 2:
            key = (1, 2)
            B = block_paths(1, key)
            old = P[1][key]
            P[1][key] = B[key]
            B[key] = old
            P.append(B)
        return [port_cycle(Q) for Q in P]

    A, B, C = (block_paths(i, pair)
               for i, pair in enumerate(((0, 1), (1, 2), (2, 0))))
    P = [
        {(0, 1): (0, 1), (1, 2): B[(1, 2)], (0, 2): A[(0, 2)]},
        {(0, 1): B[(0, 1)], (1, 2): (1, 2), (0, 2): C[(0, 2)]},
        {(0, 1): A[(0, 1)], (1, 2): C[(1, 2)], (0, 2): (0, 2)},
        {(0, 1): C[(0, 1)], (1, 2): A[(1, 2)], (0, 2): B[(0, 2)]},
    ]
    for i in range(3, k):
        Q = next(Q for Q in P if outside_count(Q) == 3)
        key = next(key for key in PAIRS if len(Q[key]) == 3)
        B = block_paths(i, key)
        old = Q[key]
        Q[key] = B[key]
        B[key] = old
        P.append(B)
    return [port_cycle(Q) for Q in P]


def expected_join_profile(k):
    if k == 1:
        return (Fraction(5, 4),) * 2
    if k == 2:
        return (Fraction(1), Fraction(5, 4), Fraction(5, 4))
    a = Fraction(3, 4) + Fraction(3, 2 * k + 2)
    b = Fraction(1) + Fraction(3, 2 * k + 2)
    return (a,) * 4 + (b,) * (k - 3)


def join_tests():
    tested = list(range(1, 21)) + [30, 50, 100, 250]
    for k in tested:
        G = join_k2(k)
        D = join_k2_fair_partition(k)
        assert len(D) == k + 1
        assert verify_partition(G, D) == expected_join_profile(k)
        assert all(G.degree(v) == 2 * k + 2 for v in range(3))
        assert all(G.degree(v) == 4 for v in G if v >= 3)
        if k <= 5:
            assert nx.node_connectivity(G) == (4 if k == 1 else 3)
        if k >= 3:
            assert Counter(sum(v >= 3 for v in C) for C in D) == Counter(
                {3: 4, 4: k - 3})
    exact = []
    for k in (1, 2, 3, 4):
        profile, D, states = fair_optimum(join_k2(k))
        assert profile == expected_join_profile(k)
        exact.append(dict(k=k, states=states, profile=list(map(str, profile))))
    return dict(family_parameters=len(tested), largest_order=2 * max(tested) + 3,
                independently_exact=exact)


def orient_even(G):
    assert all(d % 2 == 0 for _, d in G.degree())
    A = nx.DiGraph()
    A.add_nodes_from(G)
    for S in nx.connected_components(G):
        H = G.subgraph(S)
        if H.number_of_edges():
            A.add_edges_from(nx.eulerian_circuit(H))
    assert A.number_of_edges() == G.number_of_edges()
    assert all(A.in_degree(v) == A.out_degree(v) for v in A)
    return A


def directed_cycle_partition(A):
    A = A.copy()
    D = []
    while A.number_of_edges():
        start = next(v for v in A if A.out_degree(v))
        walk, at = [start], {start: 0}
        v = start
        while True:
            v = min(A.successors(v))
            if v in at:
                C = tuple(walk[at[v]:])
                assert len(C) >= 3
                A.remove_edges_from(zip(C, C[1:] + C[:1]))
                D.append(C)
                break
            at[v] = len(walk)
            walk.append(v)
    return D


def triangle_incidence_orientation(triangles):
    G = graph_from_partition(triangles)
    n = len(triangles)
    incidence = nx.Graph()
    left = [('t', i) for i in range(n)]
    for i, T in enumerate(triangles):
        assert len(T) == 3
        incidence.add_edges_from((('t', i), ('v', v)) for v in T)
    assert nx.is_connected(incidence)
    assert not list(nx.bridges(incidence))
    Q = nx.MultiGraph()
    ports = defaultdict(list)
    inc_edges = []
    for i, T in enumerate(triangles):
        for v in T:
            p = ('p', v, i)
            ports[v].append(p)
            Q.add_edge(('t', i), p, kind='incidence')
            inc_edges.append((('t', i), p, v, i))
    for v, P in ports.items():
        assert len(P) >= 2
        for j, p in enumerate(P):
            Q.add_edge(p, P[(j + 1) % len(P)], kind='port')
    assert all(d == 3 for _, d in Q.degree())
    assert nx.is_connected(Q) and not list(nx.bridges(Q))
    # Parallel edges do not change which vertex pairs can be matched.
    M = nx.max_weight_matching(nx.Graph(Q), maxcardinality=True)
    assert 2 * len(M) == len(Q)
    mate = {}
    for u, v in M:
        mate[u] = v; mate[v] = u
    selected = defaultdict(list)
    for t, p, v, i in inc_edges:
        if mate[t] != p:
            selected[i].append(v)
    F = nx.Graph()
    F.add_nodes_from(G)
    for i in range(n):
        assert len(selected[i]) == 2
        F.add_edge(*selected[i])
    assert F.number_of_edges() == n
    assert all(d % 2 == 0 for _, d in F.degree())
    AF = orient_even(F)
    A = nx.DiGraph()
    A.add_nodes_from(G)
    for i, T in enumerate(triangles):
        u, v = selected[i]
        if not AF.has_edge(u, v):
            u, v = v, u
        m = next(x for x in T if x not in (u, v))
        A.add_edges_from(((u, v), (u, m), (m, v)))
    assert {edge(u, v) for u, v in A.edges()} == set(map(lambda e: edge(*e), G.edges()))
    assert A.number_of_edges() == G.number_of_edges()
    assert all(A.in_degree(v) == A.out_degree(v) for v in A)
    for T in triangles:
        assert nx.is_directed_acyclic_graph(A.subgraph(T))
    D = directed_cycle_partition(A)
    verify_partition(G, D)
    assert not ({frozenset(T) for T in triangles} & {frozenset(C) for C in D})
    return G, D, incidence


def girth(G):
    best = len(G) + 1
    for s in G:
        dist, parent = {s: 0}, {s: None}
        queue = deque([s])
        while queue:
            v = queue.popleft()
            if 2 * dist[v] + 1 >= best:
                continue
            for u in G[v]:
                if u not in dist:
                    dist[u] = dist[v] + 1
                    parent[u] = v
                    queue.append(u)
                elif parent[v] != u:
                    best = min(best, dist[v] + dist[u] + 1)
    return best if best <= len(G) else None


def affine_triangles(h):
    points = list(product(range(3), repeat=h))
    index = {p: i for i, p in enumerate(points)}
    triples = set()
    for i, x in enumerate(points):
        for j in range(i + 1, len(points)):
            y = points[j]
            z = tuple((-a - b) % 3 for a, b in zip(x, y))
            triples.add(tuple(sorted((i, j, index[z]))))
    return sorted(triples)


def orientation_tests():
    records = []
    for name, H in [('K4', nx.complete_graph(4)),
                    ('Petersen', nx.petersen_graph()),
                    ('Heawood', nx.heawood_graph()),
                    ('dodecahedron', nx.dodecahedral_graph()),
                    ('Desargues', nx.desargues_graph())]:
        E = sorted(edge(u, v) for u, v in H.edges())
        ix = {e: i for i, e in enumerate(E)}
        triangles = [tuple(ix[edge(v, u)] for u in sorted(H[v])) for v in H]
        G, D, B = triangle_incidence_orientation(triangles)
        assert G.number_of_edges() == 2 * len(G)
        g = girth(H)
        assert girth(B) == 2 * g
        assert min(map(len, D)) >= g
        records.append(dict(example='line-' + name, n=len(G), degree=4,
                            cycles=len(D), min_weight=str(min(weight(C, original_weights(G)) for C in D)),
                            incidence_girth=2 * g))
    for h in (2, 3):
        triangles = affine_triangles(h)
        G, D, B = triangle_incidence_orientation(triangles)
        assert G.number_of_edges() == len(G) * (len(G) - 1) // 2
        assert (G.degree(0) // 2) % 3 != 0
        records.append(dict(example='affine-' + str(h), n=len(G),
                            degree=G.degree(0), cycles=len(D),
                            min_weight=str(min(weight(C, original_weights(G)) for C in D))))
    # Nonuniform occurrence degrees, still bridgeless incidence: identify an
    # independent triple in two line graphs.  No edge is identified.
    H = nx.heawood_graph()
    E = sorted(edge(u, v) for u, v in H.edges())
    ix = {e: i for i, e in enumerate(E)}
    T = [tuple(ix[edge(v, u)] for u in H[v]) for v in H]
    LG = graph_from_partition(T)
    independent = next(S for S in combinations(sorted(LG), 3)
                       if not LG.subgraph(S).number_of_edges())
    mapping = {v: v if v in independent else v + len(LG) for v in LG}
    doubled = T + [tuple(mapping[v] for v in t) for t in T]
    G, D, B = triangle_incidence_orientation(doubled)
    assert nx.node_connectivity(G) >= 3
    assert set(dict(G.degree()).values()) == {4, 8}
    records.append(dict(example='nonuniform-three-vertex-gluing', n=len(G),
                        degrees=[4, 8], cycles=len(D)))
    return records


def factor_permutations(F):
    A = orient_even(F)
    degrees = {A.out_degree(v) for v in A}
    assert len(degrees) == 1
    factors = []
    for _ in range(next(iter(degrees))):
        B = nx.Graph()
        left = [('l', v) for v in A]
        B.add_nodes_from(left, bipartite=0)
        B.add_nodes_from([('r', v) for v in A], bipartite=1)
        B.add_edges_from((('l', u), ('r', v)) for u, v in A.edges())
        M = nx.bipartite.maximum_matching(B, top_nodes=left)
        assert all(x in M for x in left)
        sigma = {v: M[('l', v)][1] for v in A}
        assert set(sigma.values()) == set(A)
        A.remove_edges_from(sigma.items())
        factors.append(sigma)
    assert not A.number_of_edges()
    return factors


def cone_partition(H):
    degree_set = {d for _, d in H.degree()}
    assert len(degree_set) == 1
    d = next(iter(degree_set))
    assert d >= 3 and d % 2 == 1
    r = (d + 1) // 2
    M = sorted(edge(u, v) for u, v in nx.max_weight_matching(H, maxcardinality=True))
    assert len(M) * 2 == len(H)
    F = H.copy()
    F.remove_edges_from(M)
    sigma = factor_permutations(F)
    assert len(sigma) == r - 1
    arms = {v: [v] for v in H}
    for p in sigma:
        assert {P[-1] for P in arms.values()} == set(H)
        for P in arms.values():
            P.append(p[P[-1]])
    paths = [tuple(reversed(arms[u])) + tuple(arms[v]) for u, v in M]
    assert all(len(P) == 2 * r and len(set(P)) == len(P) for P in paths)
    assert Counter(e for P in paths for e in path_edges(P)) == Counter(
        {edge(u, v): 1 for u, v in H.edges()})
    assert Counter(v for P in paths for v in (P[0], P[-1])) == Counter({v: 1 for v in H})
    apex = max(H) + 1
    G = H.copy()
    G.add_edges_from((apex, v) for v in H)
    D = [(apex,) + P for P in paths]
    profile = verify_partition(G, D)
    assert profile == (Fraction(1) + Fraction(1, len(H)),) * (len(H) // 2)
    assert len(D) == G.degree(apex) // 2
    assert nx.is_biconnected(H)
    assert nx.node_connectivity(G) >= 3
    return G, D


def gf4_mul(a, b):
    out = 0
    while b:
        if b & 1:
            out ^= a
        b >>= 1
        a <<= 1
        if a & 4:
            a ^= 7  # x^2+x+1
    return out


def projective_plane_four():
    def normalize(p):
        a = next(x for x in p if x)
        inv = next(b for b in range(1, 4) if gf4_mul(a, b) == 1)
        return tuple(gf4_mul(inv, x) for x in p)
    points = sorted({normalize(p) for p in product(range(4), repeat=3) if any(p)})
    assert len(points) == 21
    H = nx.Graph()
    for i, p in enumerate(points):
        for j, line in enumerate(points):
            dot = gf4_mul(p[0], line[0]) ^ gf4_mul(p[1], line[1]) ^ gf4_mul(p[2], line[2])
            if not dot:
                H.add_edge(i, len(points) + j)
    assert len(H) == 42 and all(d == 5 for _, d in H.degree())
    assert girth(H) == 6
    return H


def involution_ball(d, R):
    assert d >= 3 and d % 2 == 1 and R >= 2
    W = [()]
    for length in range(1, R + 1):
        W += [w + (i,) for w in tuple(W) if len(w) == length - 1
              for i in range(d) if not w or w[-1] != i]
    ix = {w: i for i, w in enumerate(W)}
    perms = []
    for i in range(d):
        p = list(range(len(W)))
        pairs = 0
        for w in W:
            if len(w) < R and (not w or w[-1] != i):
                a, b = ix[w], ix[w + (i,)]
                p[a], p[b] = b, a
                pairs += 1
        assert pairs == sum((d - 1) ** j for j in range(R)) and pairs % 2 == 1
        assert sorted(p) == list(range(len(W)))
        assert all(p[p[j]] == j for j in range(len(W)))
        perms.append(p)
    for w in W:
        at = ix[()]
        for i in w:
            at = perms[i][at]
        assert at == ix[w]
    return len(W)


def cone_tests():
    graphs = [('K4', nx.complete_graph(4)), ('Petersen', nx.petersen_graph()),
              ('Heawood', nx.heawood_graph()), ('cube', nx.cubical_graph()),
              ('dodecahedron', nx.dodecahedral_graph()),
              ('Desargues', nx.desargues_graph()),
              ('circular-ladder-20', nx.circular_ladder_graph(20)),
              ('projective-plane-4', projective_plane_four())]
    records = []
    for name, H in graphs:
        G, D = cone_partition(H)
        records.append(dict(example=name, n=len(G), delta=min(dict(G.degree()).values()),
                            Delta=max(dict(G.degree()).values()), count=len(D),
                            all_weights=str(weight(D[0], original_weights(G)))))
    balls = [dict(d=d, R=R, words=involution_ball(d, R))
             for d, R in ((3, 3), (3, 5), (5, 3), (5, 5), (7, 4))]
    return dict(cones=records, involution_balls=balls)


def check_block_ledger(G, D):
    blocks = [set(S) for S in nx.biconnected_components(G)]
    I = nx.Graph()
    I.add_nodes_from(('v', v) for v in G)
    owner = {}
    for i, S in enumerate(blocks):
        assert len(S) >= 3  # An even graph has no bridge block.
        I.add_edges_from((('b', i), ('v', v)) for v in S)
        for u, v in G.subgraph(S).edges():
            assert edge(u, v) not in owner
            owner[edge(u, v)] = i
    assert not I.number_of_nodes() or nx.is_forest(I)
    roots = {}
    component_roots = set()
    for S in nx.connected_components(G):
        root = min(S)
        component_roots.add(root)
        distances = nx.single_source_shortest_path_length(I, ('v', root))
        for i, B in enumerate(blocks):
            if ('b', i) in distances:
                roots[i] = min(B, key=lambda v: distances[('v', v)])
    charged = Counter(v for i, B in enumerate(blocks) for v in B if v != roots[i])
    assert charged == Counter({v: 1 for v in G if v not in component_roots})
    total = Fraction()
    for C in D:
        ids = {owner[e] for e in cycle_edges(C)}
        assert len(ids) == 1
        i = next(iter(ids))
        H = G.subgraph(blocks[i])
        assert all(d % 2 == 0 for _, d in H.degree())
        total += sum((Fraction(1, H.degree(v)) for v in C if v != roots[i]), Fraction())
    assert total == Fraction(len(G) - nx.number_connected_components(G), 2)


def atlas_tests():
    graphs = triangles = coherent = states = 0
    connected3 = []
    for i, G in enumerate(nx.graph_atlas_g()):
        if any(d % 2 for _, d in G.degree()):
            continue
        profile, D, s = fair_optimum(G)
        check_block_ledger(G, D)
        t, c = check_fair_necessary_conditions(G, D, original_weights(G))
        graphs += 1; triangles += t; coherent += c; states += s
        if len(G) >= 4 and nx.node_connectivity(G) >= 3:
            connected3.append((i, str(profile[0]), len(D)))
    assert graphs == 85
    assert len(connected3) == 10
    return dict(even_atlas_graphs=graphs, states=states, block_ledgers=graphs,
                checked_triangle_intersections=triangles,
                checked_coherent_intersections=coherent,
                three_connected=connected3)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    folder = Path(__file__).resolve().parent
    excluded = {'ResearchFairCycles.md', 'ResearchFairCyclesCheck.py'}
    before = {p.name: digest(p) for p in folder.iterdir()
              if p.is_file() and p.name not in excluded}
    assert before['Spec.lean'] == SPEC_SHA256
    results = {}
    for name, run in [('coherent_and_triangle', coherent_and_triangle_tests),
                      ('join_k2', join_tests),
                      ('orientation', orientation_tests),
                      ('cones', cone_tests),
                      ('atlas', atlas_tests)]:
        results[name] = run()
        print(name + ': ' + json.dumps(results[name], sort_keys=True), flush=True)
    after = {p.name: digest(p) for p in folder.iterdir()
             if p.is_file() and p.name not in excluded}
    assert before == after
    print('PASS: all exact checks; %d protected files unchanged.' % len(before))


if __name__ == '__main__':
    main()
