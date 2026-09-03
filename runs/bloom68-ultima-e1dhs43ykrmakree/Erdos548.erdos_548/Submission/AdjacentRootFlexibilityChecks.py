#!/usr/bin/env python3
"""Exact, structured audits for AdjacentRootFlexibilityFindings.md.

Run: python3 Submission/AdjacentRootFlexibilityChecks.py
Requires networkx. No random search, ES oracle, or changes to Lean files.
"""
from __future__ import annotations

from collections import Counter
from itertools import combinations
from pathlib import Path
import hashlib
import networkx as nx

ST = Counter()
SPEC_SHA = "674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103"
HERE = Path(__file__).resolve().parent


def arc_builder():
    G, D = nx.Graph(), nx.DiGraph()

    def arc(u, v):
        assert u != v and not G.has_edge(u, v), (u, v)
        G.add_edge(u, v)
        D.add_edge(u, v)

    return G, D, arc


def star_with_handle(degree, length):
    """Hub 0, degree-1 short leaves, and one arm of length `length`."""
    T = nx.Graph()
    leaves = list(range(1, degree))
    arm = list(range(degree, degree + length))
    T.add_edges_from((0, v) for v in leaves)
    T.add_edges_from(zip([0] + arm, arm))
    assert nx.is_tree(T)
    assert T.degree(0) == degree
    assert T.number_of_edges() == degree - 1 + length
    return T, leaves, arm


def graph20():
    G, D, arc = arc_builder()
    s = 0
    paths = [[1, 2], [3, 4], [5, 6, 7]]
    endpoints = [1, 2, 3, 4, 5, 7]
    C, P = list(range(8, 14)), list(range(14, 20))
    for path in paths:
        arc(s, path[0])
        for x, y in zip(path, path[1:]):
            arc(x, y)
        for x in path[1:]:
            arc(x, s)
    for a, c in zip(endpoints, C):
        arc(a, c)
    for i, c in enumerate(C):
        arc(c, P[i])
        arc(c, P[(i + 1) % 6])
    for i, p in enumerate(P):
        for h in (1, 2):
            arc(p, P[(i + h) % 6])
    rooted = {0: s, 4: 1, 5: C[0], 1: 2, 2: 3, 3: 4}
    away = {0: P[0], 4: P[1], 5: P[3], 1: P[2], 2: P[4], 3: P[5]}
    return G, D, s, C, P, rooted, away


def graph32_bipartite():
    G, D, arc = arc_builder()
    s, endpoints, middle = 0, [], []
    for i in range(3):
        path = list(range(1 + 5 * i, 6 + 5 * i))
        arc(s, path[0])
        for x, y in zip(path, path[1:]):
            arc(x, y)
        arc(path[2], s)
        arc(path[4], s)
        endpoints.extend((path[0], path[4]))
        middle.extend((path[1], path[3]))
    C = list(range(16, 22))
    X, Y = list(range(22, 27)), list(range(27, 32))
    for a, c in zip(endpoints, C):
        arc(a, c)
    # K_(5,5) minus the matching X_i Y_i, oriented with outdegree two.
    for i in range(5):
        for h in (1, 2):
            arc(X[i], Y[(i + h) % 5])
        for h in (3, 4):
            arc(Y[(i + h) % 5], X[i])
    for i, c in enumerate(C):
        arc(c, Y[(2 * i) % 5])
        arc(c, Y[(2 * i + 1) % 5])
    for j, b in enumerate(middle):
        arc(b, Y[(12 + j) % 5])
    rooted = {0: s, 4: endpoints[0], 5: C[0],
              1: endpoints[1], 2: endpoints[2], 3: endpoints[3]}
    away = {0: X[0], 4: Y[1], 5: X[2], 1: Y[2], 2: Y[3], 3: Y[4]}
    return G, D, s, C, X + Y, rooted, away


def general_graph(r):
    """An r-circuit with all non-root vertices in B_2(s) of degree r+1."""
    assert r >= 2
    G, D, arc = arc_builder()
    s, nxt, A, C, child_parent = 0, 1, [], [], {}
    for _ in range(r + 1):
        a, b = nxt, nxt + 1
        nxt += 2
        A.extend((a, b))
        arc(s, a)
        arc(a, b)
        arc(b, s)
        for x in (a, b):
            for _ in range(r - 1):
                c = nxt
                nxt += 1
                C.append(c)
                child_parent[c] = x
                arc(x, c)
    N = r * len(C)
    P = list(range(nxt, nxt + N))
    child_ports = {}
    for i, c in enumerate(C):
        child_ports[c] = P[r * i:r * (i + 1)]
        for p in child_ports[c]:
            arc(c, p)
    for i, p in enumerate(P):
        for h in range(1, r + 1):
            arc(p, P[(i + h) % N])
    assert len(G) == 1 + 2 * r * r * (r + 1)
    assert len(P) == 2 * r * (r * r - 1)
    return G, D, s, A, C, P, child_parent, child_ports


def check_copy(T, G, f, prescribed=None):
    assert set(f) == set(T)
    assert len(set(f.values())) == len(T)
    assert set(f.values()) <= set(G)
    assert all(G.has_edge(f[u], f[v]) for u, v in T.edges())
    if prescribed is not None:
        u, s = prescribed
        assert f[u] == s
    ST["explicit injective tree copies"] += 1


def check_orientation(G, D, s, r):
    assert set(G) == set(D)
    assert G.number_of_edges() == D.number_of_edges()
    assert {frozenset(e) for e in G.edges()} == {frozenset(e) for e in D.edges()}
    assert D.out_degree(s) == r + 1
    assert all(D.out_degree(v) == r for v in G if v != s)
    assert nx.descendants(D, s) == set(G) - {s}
    assert G.number_of_edges() == r * len(G) + 1
    assert G.degree(s) > max(G.degree(v) for v in G if v != s)
    ST["root-reachable circuit orientation certificates"] += 1


def all_induced_subsets(G, r):
    """An independent direct integer check, used only for the 20-vertex host."""
    n = len(G)
    assert set(G) == set(range(n)) and G.number_of_edges() < 256
    adj = [sum(1 << w for w in G[v]) for v in range(n)]
    edges = bytearray(1 << n)
    full, tight_nonempty = (1 << n) - 1, 0
    for S in range(1, full + 1):
        bit = S & -S
        v, R = bit.bit_length() - 1, S ^ bit
        edges[S] = edges[R] + (adj[v] & R).bit_count()
        surplus = edges[S] - r * S.bit_count()
        if S != full:
            assert surplus <= 0, (S, surplus)
            tight_nonempty += surplus == 0
        else:
            assert surplus == 1
    ST["proper induced subsets checked exhaustively (including empty)"] += full
    return tight_nonempty


def all_proper_sets_by_min_cut(G, r):
    """Max-closure checks e(S)-r|S| with each possible omitted vertex.

    Each edge-node has reward 1 and requires its two endpoint-nodes;
    each vertex-node has cost r. An excluded vertex has prohibitive cost.
    This independently maximizes over ALL subsets, not sampled subsets.
    """
    F = nx.DiGraph()
    source, sink = ("source",), ("sink",)
    m, INF = G.number_of_edges(), G.number_of_edges() + 1
    for v in G:
        F.add_edge(("v", v), sink, capacity=r)
    for i, (u, v) in enumerate(G.edges()):
        e = ("e", i)
        F.add_edge(source, e, capacity=1)
        F.add_edge(e, ("v", u), capacity=INF)
        F.add_edge(e, ("v", v), capacity=INF)
    for excluded in list(G) + [None]:
        if excluded is not None:
            F[("v", excluded)][sink]["capacity"] = INF
        value, partition = nx.minimum_cut(F, source, sink)
        surplus = m - value
        chosen = {v for v in G if ("v", v) in partition[0]}
        assert G.subgraph(chosen).number_of_edges() - r * len(chosen) == surplus
        if excluded is not None:
            assert excluded not in chosen and surplus == 0
            F[("v", excluded)][sink]["capacity"] = r
            ST["proper-set exclusion min-cuts"] += 1
        else:
            assert surplus == 1 and chosen == set(G)
            ST["unconstrained surplus min-cuts"] += 1


def check_three_connected(G, degree_three_vertex):
    for j in range(3):
        for deleted in combinations(G, j):
            assert nx.is_connected(G.subgraph(set(G) - set(deleted)))
            ST["connectivity checks after at most two deletions"] += 1
    cut = set(G[degree_three_vertex])
    assert len(cut) == 3
    assert not nx.is_connected(G.subgraph(set(G) - cut))
    ST["explicit three-vertex cut witnesses"] += 1


def check_wk(G, k):
    active, order = set(), []
    while len(active) != len(G):
        eligible = [v for v in sorted(G) if v not in active
                    and G.degree(v) + len(set(G[v]) & active) >= k]
        assert eligible
        v = eligible[0]
        order.append(v)
        active.add(v)
    ST["W_k activation orders"] += 1
    return order


def classify_by_degree_ball(T, G, s, hub, allowed_maps):
    """Certify all excluded roles by degree, all included roles by injections."""
    allowed = set(allowed_maps)
    for u, f in allowed_maps.items():
        check_copy(T, G, f, (u, s))
    dist = nx.single_source_shortest_path_length(T, hub)
    for u in set(T) - allowed:
        assert u != hub
        ball = nx.single_source_shortest_path_length(G, s, cutoff=dist[u])
        assert all(G.degree(v) < T.degree(hub) for v in ball if v != s)
        ST["excluded roles certified by the degree-ball lemma"] += 1
    ST["exact permissible-role sets certified"] += 1
    return allowed


def graphmatcher_roles(T, G, s):
    roles = set()
    for u in T:
        H, F = G.copy(), T.copy()
        nx.set_node_attributes(H, False, "root")
        nx.set_node_attributes(F, False, "root")
        H.nodes[s]["root"] = F.nodes[u]["root"] = True
        matcher = nx.algorithms.isomorphism.GraphMatcher(
            H, F, node_match=lambda a, b: a["root"] == b["root"])
        f = next(matcher.subgraph_monomorphisms_iter(), None)
        if f is not None:
            roles.add(u)
            check_copy(T, G, {b: a for a, b in f.items()}, (u, s))
        ST["independent rooted monomorphism decisions"] += 1
    return roles


def small_counterexamples():
    T, _, arm = star_with_handle(4, 2)
    assert arm == [4, 5] and T.has_edge(*arm)
    for name, builder in (("20-vertex", graph20),
                          ("32-vertex bipartite", graph32_bipartite)):
        G, D, s, C, P, rooted, away = builder()
        check_orientation(G, D, s, 2)
        assert min(dict(G.degree()).values()) == 3
        assert set(nx.single_source_shortest_path_length(G, s, cutoff=2)) == set(G) - set(P)
        assert all(G.degree(v) == 3 for v in set(G) - set(P) - {s})
        all_proper_sets_by_min_cut(G, 2)
        check_three_connected(G, C[0])
        order = check_wk(G, 5)
        roles = classify_by_degree_ball(T, G, s, 0, {0: rooted})
        assert roles == {0} == graphmatcher_roles(T, G, s)
        assert not roles.intersection(arm)
        assert set(away.values()) <= set(P)
        check_copy(T, G, away)
        if len(G) == 20:
            tight = all_induced_subsets(G, 2)
            assert tight == 99
            print(f"{name}: all 1,048,575 proper subsets sparse; "
                  f"{tight} nonempty proper tight subsets")
            # Both marked interfaces for the edge 4--5 fail.
            H = G.subgraph(set(G) - {s})
            assert all(H.degree(v) == 2 for v in G[s])
            assert H.number_of_edges() == 34 > len(H)  # parameter k-2=3
        else:
            assert nx.is_bipartite(G)
        print(f"{name}: n={len(G)}, m={G.number_of_edges()}, "
              f"eta=1, unique maximum degree={G.degree(s)}, connectivity=3, R_s={sorted(roles)}")
        print(f"  W_5 order: {order}")


def infinite_family_audit():
    for r in range(2, 9):
        G, D, s, A, C, P, parent, ports = general_graph(r)
        check_orientation(G, D, s, r)
        assert G.degree(s) == 2 * r + 2
        assert all(G.degree(p) == 2 * r + 1 for p in P)
        assert all(G.degree(v) == r + 1 for v in A + C)
        assert set(nx.single_source_shortest_path_length(G, s, cutoff=2)) == {s} | set(A + C)
        a, c = parent[C[0]], C[0]
        p = ports[c][0]
        reservoir_neighbors = sorted(set(G[P[0]]) & set(P))

        T, leaves, arm = star_with_handle(2 * r, 2)
        rooted = {0: s, arm[0]: a, arm[1]: c}
        rooted.update(zip(leaves, [v for v in A if v != a]))
        away = {0: P[0], arm[0]: P[1], arm[1]: P[r + 1]}
        away.update(zip(leaves, [v for v in reservoir_neighbors if v != P[1]]))
        roles = classify_by_degree_ball(T, G, s, 0, {0: rooted})
        assert roles == {0} and not roles.intersection(arm)
        check_copy(T, G, away)

        if r >= 3:
            U, leaves, arm = star_with_handle(2 * r - 1, 3)
            rooted = {0: s, arm[0]: a, arm[1]: c, arm[2]: p}
            rooted.update(zip(leaves, [v for v in A if v != a]))
            leaf_rooted = {arm[2]: s, arm[1]: a, arm[0]: c, 0: p}
            leaf_rooted.update(zip(leaves, sorted(set(G[p]) & set(P))))
            away = {0: P[0], arm[0]: P[1], arm[1]: P[r + 1], arm[2]: P[r + 2]}
            away.update(zip(leaves, [v for v in reservoir_neighbors if v != P[1]]))
            roles = classify_by_degree_ball(U, G, s, 0, {0: rooted, arm[2]: leaf_rooted})
            assert roles == {0, arm[2]}
            assert U.has_edge(arm[0], arm[1])
            assert U.degree(arm[0]) == U.degree(arm[1]) == 2
            assert not roles.intersection(arm[:2])
            check_copy(U, G, away)
            ST["adjacent unavailable nonleaf-edge examples"] += 1
        ST["odd-parameter family instances"] += 1
    print("Infinite-family audit: r=2,...,8; R_s={hub} for the length-two broom")
    print("  r=3,...,8: both internal vertices of the length-three arm are unavailable")


def main():
    before = {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in HERE.glob("*.lean")}
    assert before[HERE / "Spec.lean"] == SPEC_SHA
    small_counterexamples()
    infinite_family_audit()
    assert before == {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in HERE.glob("*.lean")}
    print("PASS")
    for key, value in sorted(ST.items()):
        print(f"{key}: {value:,}")
    print(f"Lean files unchanged during checks: {len(before)}")
    print(f"Spec.lean SHA-256: {SPEC_SHA}")


if __name__ == "__main__":
    main()
