#!/usr/bin/env python3
"""Exact audits of the global two-budget/palette lemma.

Embeddings are non-induced. All flow arithmetic is integral after scaling;
all reported identities are rechecked with fractions. This is not an
Erdos--Sos solver. No imports from Submission.Spec or earlier audit scripts.
"""
from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import combinations
from math import gcd, lcm
import argparse
import hashlib
import json
import random
import time
import networkx as nx

SPEC_HASH = '674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103'


def edge(u, v):
    return (min(u, v), max(u, v))


def critical(G, k):
    n = len(G)
    if set(G) != set(range(n)):
        raise ValueError('use consecutive labels')
    surplus = 2 * G.number_of_edges() - (k - 1) * n
    if surplus not in (1, 2):
        return False
    adj = [sum(1 << w for w in G[v]) for v in G]
    counts = [0] * (1 << n)
    for S in range(1, (1 << n) - 1):
        bit = S & -S
        v = bit.bit_length() - 1
        rest = S ^ bit
        counts[S] = counts[rest] + (adj[v] & rest).bit_count()
        if 2 * counts[S] > (k - 1) * S.bit_count():
            return False
    return True


def weighted_degree_F(F, extra, eps):
    d = {v: Q(F.degree(v)) for v in F}
    if F.has_edge(*extra):
        for v in extra:
            d[v] -= eps
    return max(d.values(), default=Q(0))


def palette_flow(G, k, F, extra, beta):
    a = Q(k - 1, 2)
    eps = Q(G.number_of_edges()) - a * len(G)
    assert eps in (Q(1, 2), Q(1))
    directed_extra = tuple(extra)
    extra = edge(*extra)
    beta = Q(beta)
    alpha = a - beta
    assert 0 <= beta <= a and G.has_edge(*extra)
    assert all(G.has_edge(u, v) for u, v in F.edges())
    assert weighted_degree_F(F, extra, eps) <= beta
    scale = lcm(a.denominator, beta.denominator, eps.denominator)
    N = nx.DiGraph()
    source, sink = ('source',), ('sink',)
    N.add_nodes_from([source, sink])
    edges = [edge(u, v) for u, v in G.edges()]
    total = 0
    for i, (u, v) in enumerate(edges):
        w = Q(1) - (eps if (u, v) == extra else 0)
        if not w:
            continue
        cap = int(scale * w)
        total += cap
        enode = ('e', i)
        N.add_edge(source, enode, capacity=cap)
        colors = ('B',) if F.has_edge(u, v) else ('B', 'R')
        for z in (u, v):
            for c in colors:
                N.add_edge(enode, (c, z), capacity=cap)
    for v in G:
        N.add_edge(('B', v), sink, capacity=int(scale * beta))
        N.add_edge(('R', v), sink, capacity=int(scale * alpha))
    value, flow = nx.maximum_flow(N, source, sink)
    assert value == total == int(scale * a * len(G))
    blue, red = defaultdict(Q), defaultdict(Q)
    for i, (u, v) in enumerate(edges):
        node = ('e', i)
        if node not in flow:
            continue
        for x, y in [(u, v), (v, u)]:
            blue[x, y] += Q(flow[node].get(('B', x), 0), scale)
            red[x, y] += Q(flow[node].get(('R', x), 0), scale)
    blue[directed_extra] += eps
    verify_flow(G, k, F, directed_extra, beta, blue, red)
    return blue, red


def reachable(blue, root):
    C = {root}
    stack = [root]
    adj = defaultdict(list)
    for (u, v), w in blue.items():
        if w > 0:
            adj[u].append(v)
    while stack:
        u = stack.pop()
        for v in adj[u]:
            if v not in C:
                C.add(v)
                stack.append(v)
    return C


def incident(G, X):
    return sum(u in X or v in X for u, v in G.edges())


def verify_flow(G, k, F, extra, beta, blue, red):
    a = Q(k - 1, 2)
    eps = Q(G.number_of_edges()) - a * len(G)
    alpha = a - beta
    u0, v0 = extra
    for u, v in G.edges():
        assert blue.get((u, v), 0) >= 0 and blue.get((v, u), 0) >= 0
        assert red.get((u, v), 0) >= 0 and red.get((v, u), 0) >= 0
        assert sum(A.get((x, y), 0) for A in (blue, red)
                   for x, y in ((u, v), (v, u))) == 1
        if F.has_edge(u, v):
            assert red.get((u, v), 0) + red.get((v, u), 0) == 0
    assert blue[u0, v0] >= eps
    for v in G:
        assert sum(w for (x, y), w in red.items() if x == v) == alpha
        assert sum(w for (x, y), w in blue.items() if x == v) == beta + (eps if v == u0 else 0)
    C = reachable(blue, u0)
    X = set(G) - C
    assert {u0, v0} <= C
    assert sum(w for (u, v), w in blue.items() if u in C and v in C) == beta * len(C) + eps
    assert sum(w for (u, v), w in blue.items() if u in X or v in X) == beta * len(X)
    escape = sum(w for (u, v), w in red.items() if u in C and v in X)
    assert incident(G, X) == a * len(X) + escape
    if X:
        assert escape > 0
    D = set(F) - C
    for R in nx.connected_components(F.subgraph(D)):
        e = F.subgraph(R).number_of_edges()
        b = sum((u in R and v in C) or (v in R and u in C) for u, v in F.edges())
        assert e + b <= beta * len(R)
        if nx.is_tree(F.subgraph(R)):
            assert b <= (beta - 1) * len(R) + 1
    return C, X, escape


def blocked_leaf_obstruction(r):
    """A maximal proper tree state: F=T-leaf, with no unused parent neighbor."""
    assert r >= 3
    N = 2 * r + 1
    u, v = N, N + 1
    G = nx.complete_graph(N)
    A = set(range(r))
    B = {0, 1} | set(range(r + 1, 2 * r - 1))
    assert len(B) == r
    G.add_edges_from((u, a) for a in A)
    G.add_edges_from((v, b) for b in B)
    G.add_edge(u, v)
    F = nx.Graph([(u, 0), (u, 2), (v, 0), (v, 1), (v, 2 * r - 2)])
    F.add_edges_from((j, j + 1) for j in range(2, 2 * r - 3))
    assert nx.is_tree(F) and F.number_of_edges() == 2 * r
    assert len(F) == 2 * r + 1 and max(dict(F.degree()).values()) == 3
    assert [z for z in F if F.degree(z) == 3] == [v]
    assert set(G[u]) <= set(F)
    assert set(G) - set(F) == {2 * r - 1, 2 * r}
    T = F.copy()
    leaf = N + 2
    T.add_edge(u, leaf)
    assert nx.is_tree(T) and T.number_of_edges() == 2 * r + 1
    assert max(dict(T.degree()).values()) == 3 <= r
    assert sum(T.degree(z) >= 3 for z in T) == 2
    # The specified F has zero extensions, but T embeds after global relabeling.
    im = {leaf: u, u: 0}
    im.update(zip([z for z in T if z not in im], range(1, N)))
    assert len(set(im.values())) == len(T)
    assert all(G.has_edge(im[a], im[b]) for a, b in T.edges())
    return G, F, (0, v), T, im


def explicit_blocked_leaf_flow(r):
    G, F, extra, T, im = blocked_leaf_obstruction(r)
    N = 2 * r + 1
    u, v = N, N + 1
    blue, red = defaultdict(Q), defaultdict(Q)
    for i in range(1, r + 1):
        arcs = [(j, (j + i) % N) for j in range(N)]
        if i == 1:
            arcs += [(u, 0), (v, 1)]
            color = blue
        elif i == 2:
            arcs += [(u, 2), (v, 2 * r - 2)]
            color = blue
        else:
            j = i - 2
            if j == 1:
                arcs += [(v, u), (u, 1)]
            else:
                arcs += [(u, j + 1), (v, r + j - 1)]
            color = red
        M = nx.Graph()
        M.add_nodes_from(G)
        M.add_edges_from(arcs)
        assert M.number_of_edges() == len(G)
        assert all(M.subgraph(C).number_of_edges() == len(C) for C in nx.connected_components(M))
        if color is red:
            assert not any(F.has_edge(a, b) for a, b in M.edges())
        for a, b in arcs:
            color[a, b] += Q(1)
    blue[v, 0] += 1
    C, X, escape = verify_flow(G, 2 * r + 1, F, (v, 0), Q(2), blue, red)
    assert C == set(range(N)) | {v}
    assert X == {u} and escape == red[v, u] == 1
    assert nx.number_connected_components(F.subgraph(C & set(F))) == 2
    assert sum(w for (a, b), w in blue.items() if b == u) == 0
    assert not (set(G[u]) - set(F))
    return G, F


def obstruction(r, q=2):
    """r-circuit, (2r-1)-edge F, Delta(F)=q+1, pinned extra u0."""
    assert 2 <= q <= r - 1
    N = 2 * r + 1
    u, v = N, N + 1
    W = set(range(N))
    A = set(range(r))
    B = {0} | set(range(r, 2 * r - 1))
    G = nx.complete_graph(N)
    G.add_edges_from((u, x) for x in A)
    G.add_edges_from((v, x) for x in B)
    G.add_edge(u, v)
    F = nx.Graph()
    F.add_edges_from((u, x) for x in range(q + 1))
    BF = {0} | set(range(2 * r - q, 2 * r - 1))
    F.add_edges_from((v, x) for x in BF)
    for x in range(q, 2 * r - q - 2):
        F.add_edge(x, x + 1)
    extra = (0, u)
    # To orient the extra away from u in the explicit certificate use (u,0).
    # palette_flow normalizes it, so its root is 0; both endpoints remain in C,
    # and the zero-blue-indegree obstruction at v is unaffected.
    assert nx.is_tree(F) and F.number_of_edges() == 2 * r - 1
    assert len(F) == 2 * r and max(dict(F.degree()).values()) == q + 1
    assert F.degree(u) == q + 1 and F.degree(v) == q
    assert weighted_degree_F(F, extra, Q(1)) == q
    # Extend F by two sibling leaves at one of v's other neighbors.
    b = min(BF - {0})
    T = F.copy()
    T.add_edges_from([(b, N + 2), (b, N + 3)])
    assert nx.is_tree(T) and T.number_of_edges() == 2 * r + 1
    assert max(dict(T.degree()).values()) == q + 1 <= r
    assert sum(T.degree(x) >= 3 for x in T) >= 2
    # A full non-induced T-copy in G: send a leaf to host u, the rest into W.
    leaf = next(x for x in T if T.degree(x) == 1)
    parent = next(iter(T[leaf]))
    im = {leaf: u, parent: 0}
    others = [x for x in T if x not in im]
    im.update(zip(others, range(1, N)))
    assert len(set(im.values())) == len(T)
    assert all(G.has_edge(im[x], im[y]) for x, y in T.edges())
    return G, F, extra, T, im


def explicit_obstruction_flow(r, q):
    G, F, extra, T, im = obstruction(r, q)
    N = 2 * r + 1
    u, v = N, N + 1
    s = r - q
    maps = []
    blue, red = defaultdict(Q), defaultdict(Q)
    for i in range(1, r + 1):
        arcs = [(j, (j + i) % N) for j in range(N)]
        if i <= q:
            b = 0 if i == 1 else 2 * r - q + i - 2
            arcs += [(u, i), (v, b)]
            color = blue
        else:
            j = i - q
            if j == 1:
                arcs += [(u, v), (v, r)]
            else:
                arcs += [(u, q + j - 1), (v, r + j - 1)]
            color = red
        M = nx.Graph()
        M.add_nodes_from(G)
        M.add_edges_from(arcs)
        assert len(arcs) == len(G) == M.number_of_edges()
        assert all(M.subgraph(C).number_of_edges() == len(C) for C in nx.connected_components(M))
        if i > q:
            assert not set(map(lambda e: edge(*e), M.edges())) & set(map(lambda e: edge(*e), F.edges()))
        for a, b in arcs:
            color[a, b] += Q(1)
        maps.append(M)
    blue[u, 0] += Q(1)
    C, X, escape = verify_flow(G, 2 * r + 1, F, (u, 0), Q(q), blue, red)
    assert C == set(range(N)) | {u} and X == {v}
    assert escape == 1
    assert nx.number_connected_components(F.subgraph(C & set(F))) == q
    assert sum(w for (a, b), w in blue.items() if b == v) == 0
    assert all(x.denominator == 1 for D in (blue, red) for x in D.values())
    # Independent q-sparsity audit on the displayed lower core for small cases.
    if len(C) <= 14:
        H = nx.Graph()
        H.add_nodes_from(C)
        H.add_edges_from((a, b) for (a, b), w in blue.items() if w and a in C and b in C)
        H = nx.convert_node_labels_to_integers(H)
        assert critical(H, 2 * q + 1)
    return G, F


def random_tree_copy(G, m, D, rng):
    for _ in range(30):
        F = nx.Graph()
        F.add_node(rng.choice(list(G)))
        for _ in range(m):
            candidates = [(u, v) for u in F if F.degree(u) < D for v in G[u] if v not in F]
            if not candidates:
                break
            F.add_edge(*rng.choice(candidates))
        if F.number_of_edges() == m:
            return F
    return None


def run(atlas_samples=5000):
    start = time.time()
    assert hashlib.sha256(open('Submission/Spec.lean', 'rb').read()).hexdigest() == SPEC_HASH
    counts = Counter()
    # Exact type-by-type criticality verification for the clique-plus-two-vertices
    # family. For each clique size and added-vertex count, use a uniform upper
    # bound valid for every neighbor intersection, not a vertex sample.
    for r in range(2, 101):
        N = 2 * r + 1
        for x in range(N + 1):
            for ext in range(3):
                if x == N and ext == 2:
                    continue
                # Safe upper bounds. For x=0 the only possible extra edge is uv.
                bound = x * (x - 1) // 2 + ext * min(r, x) + int(ext == 2)
                assert bound <= r * (x + ext)
                counts['critical_subset_type_bounds'] += 1
    # Direct, not type-based, subset audits of the small displayed hosts.
    for r in range(3, 7):
        G, _, _, _, _ = obstruction(r, 2)
        assert critical(G, 2 * r + 1)
        counts['direct_critical_subset_audits'] += (1 << len(G)) - 2
    # Maximal leaf-deleted states: all eligible pinned edges and both directions.
    for r in range(3, 41):
        G, F, extra, T, im = blocked_leaf_obstruction(r)
        u, v = 2 * r + 1, 2 * r + 2
        if r <= 6:
            assert critical(G, 2 * r + 1)
            counts['blocked_leaf_direct_subset_audits'] += (1 << len(G)) - 2
        explicit_blocked_leaf_flow(r)
        counts['blocked_leaf_explicit_decompositions'] += 1
        eligible = [edge(a, b) for a, b in F.edges()
                    if weighted_degree_F(F, (a, b), Q(1)) <= 2]
        assert set(eligible) == {edge(v, w) for w in F[v]}
        assert len(eligible) == 3
        for e0 in eligible:
            for directed in [e0, tuple(reversed(e0))]:
                B, R = palette_flow(G, 2 * r + 1, F, directed, 2)
                C = reachable(B, directed[0])
                assert v in C and u not in C
                assert R[v, u] == 1
                assert sum(w for (a, b), w in B.items() if b == u) == 0
                assert not (set(G[u]) - set(F))
                counts['blocked_leaf_all_pin_flow_checks'] += 1
    # Explicit integral decompositions for every rank pair in this range.
    for r in range(3, 31):
        for q in range(2, r):
            explicit_obstruction_flow(r, q)
            counts['explicit_obstruction_decompositions'] += 1
            if q == r - 1 and r >= 5:
                counts['disconnected_intersection_families'] += 1
    # Independently find flows by max flow, and verify that v cannot enter C.
    for r in range(3, 31):
        for q in sorted({2, r - 1}):
            G, F, extra, T, im = obstruction(r, q)
            B, R = palette_flow(G, 2 * r + 1, F, extra, q)
            C = reachable(B, extra[0])
            assert 2 * r + 2 not in C
            assert sum(w for (a, b), w in B.items() if b == 2 * r + 2) == 0
            if q == r - 1 and r >= 5:
                assert nx.number_connected_components(F.subgraph(C & set(F))) >= r - 3
            counts['independent_obstruction_flows'] += 1
    # All qualifying critical atlas hosts, sampled protected tree/extra-edge pairs.
    cores = []
    for G in nx.graph_atlas_g():
        if len(G) < 3:
            continue
        for k in range(2, len(G)):
            if critical(G, k):
                cores.append((G, k))
    counts['critical_atlas_hosts'] = len(cores)
    rng = random.Random(1518801)
    for _ in range(atlas_samples):
        G, k = rng.choice(cores)
        m = rng.randint(1, min(k - 1, 4))
        F = random_tree_copy(G, m, max(2, k // 2), rng)
        if F is None:
            continue
        extra = edge(*rng.choice(list(F.edges())))
        a = Q(k - 1, 2)
        eps = Q(G.number_of_edges()) - a * len(G)
        beta = weighted_degree_F(F, extra, eps)
        if beta > a:
            continue
        B, R = palette_flow(G, k, F, extra, beta)
        C = reachable(B, extra[0])
        counts['atlas_fractional_flows'] += 1
        counts['even_flows' if k % 2 == 0 else 'odd_flows'] += 1
        counts['spanning_blue_reachable' if len(C) == len(G) else 'nonspanning_blue_reachable'] += 1
        if any(w.denominator != 1 for A in (B, R) for w in A.values()):
            counts['genuinely_fractional_flows'] += 1
    # Non-half-integral rational budgets: the proof is not restricted to two
    # integral functional palettes or to the parity denominators of G.
    for _ in range(400):
        G, k = rng.choice(cores)
        F = random_tree_copy(G, min(k - 1, 3), max(2, k // 2), rng)
        assert F is not None
        extra = edge(*rng.choice(list(F.edges())))
        a = Q(k - 1, 2)
        eps = Q(G.number_of_edges()) - a * len(G)
        lower = weighted_degree_F(F, extra, eps)
        if lower >= a:
            continue
        beta = (2 * lower + a) / 3
        B, R = palette_flow(G, k, F, extra, beta)
        counts['additional_rational_budget_flows'] += 1
        if any(w.denominator not in (1, 2) for A in (B, R) for w in A.values()):
            counts['nonhalf_integral_outputs'] += 1
    # Even critical split graphs: epsilon=1 in doubled units; non-spider,
    # bounded-degree partial trees, including the deficient-degree range.
    for a in range(4, 21):
        b = a * a + 1
        G = nx.Graph()
        G.add_nodes_from(range(a + b))
        G.add_edges_from(combinations(range(a), 2))
        G.add_edges_from((x, y) for x in range(a) for y in range(a, a + b))
        for x in range(a + 1):
            for y in range(b + 1):
                if x == a and y == b:
                    continue
                assert x * (x - 2 * a) + (2 * x - 2 * a + 1) * y <= 0
                counts['split_subset_type_bounds'] += 1
        assert 2 * G.number_of_edges() - (2 * a - 1) * len(G) == 1
        for _ in range(5):
            F = random_tree_copy(G, 2 * a - 2, 3, rng)
            assert F is not None
            e0 = edge(*rng.choice(list(F.edges())))
            beta = weighted_degree_F(F, e0, Q(1, 2))
            assert beta <= 3 < Q(2 * a - 1, 2)
            palette_flow(G, 2 * a, F, e0, beta)
            counts['even_large_split_flows'] += 1
    assert hashlib.sha256(open('Submission/Spec.lean', 'rb').read()).hexdigest() == SPEC_HASH
    report = {'status': 'ALL CHECKS PASSED', 'counts': dict(counts), 'seconds': round(time.time() - start, 3), 'spec_sha256': SPEC_HASH}
    print(json.dumps(report, indent=2))
    return report


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--atlas-samples', type=int, default=5000)
    p.add_argument('--json', type=str)
    args = p.parse_args()
    result = run(args.atlas_samples)
    if args.json:
        with open(args.json, 'w') as f:
            json.dump(result, f, indent=2)
