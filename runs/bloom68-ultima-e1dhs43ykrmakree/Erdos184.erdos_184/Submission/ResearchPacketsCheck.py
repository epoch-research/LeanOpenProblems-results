#!/usr/bin/env python3
"""Independent finite checks for ResearchPackets.md; never edits Spec.lean.

Requires the already available networkx, numpy, and scipy packages.
The general mathematical assertions are proved in the Markdown record;
these finite checks are not substitutes for those proofs.
"""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
from hashlib import sha256
import random

import networkx as nx
import numpy as np
from scipy.optimize import minimize

SPEC_SHA256 = "429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde"


def edge_set(path):
    return {frozenset(e) for e in zip(path, path[1:])}


def route_qp(R, pairs):
    edges = list(R.edges())
    index = {frozenset(e): k for k, e in enumerate(edges)}
    paths, groups = [], []
    for s, t in pairs:
        ids = []
        for path in nx.all_simple_paths(R, s, t):
            ids.append(len(paths))
            paths.append(path)
        assert ids
        groups.append(ids)
    B = np.zeros((len(edges), len(paths)))
    for j, path in enumerate(paths):
        for e in edge_set(path):
            B[index[e], j] = 1
    C = np.zeros((len(pairs), len(paths)))
    x0 = np.zeros(len(paths))
    for i, ids in enumerate(groups):
        C[i, ids] = 1
        x0[ids] = 1 / len(ids)
    result = minimize(
        lambda x: 0.5 * np.sum((B @ x) ** 2), x0,
        jac=lambda x: B.T @ (B @ x),
        constraints=[{"type": "eq", "fun": lambda x: C @ x - 1,
                      "jac": lambda x: C}],
        bounds=[(0, 1)] * len(paths), method="SLSQP",
        options={"ftol": 1e-13, "maxiter": 1000},
    )
    assert result.success, result.message
    load = B @ result.x
    marginals = np.array([B[:, ids] @ result.x[ids] for ids in groups])
    marginal_price = marginals @ load
    external_price = np.array([
        marginals[i] @ (load - marginals[i]) for i in range(len(pairs))
    ])
    return result.fun, load, marginal_price, external_price


def close(actual, expected, tol=1e-7):
    assert np.allclose(actual, expected, atol=tol, rtol=tol), (actual, expected)


def check_small_qps():
    pairings = [[("a", "b"), ("c", "d")],
                [("a", "d"), ("b", "c")],
                [("a", "c"), ("b", "d")]]
    R = nx.Graph(list(combinations("abcd", 2)))
    G = R.copy()
    G.add_edges_from(("v", t) for t in "abcd")
    assert G.number_of_nodes() == 5
    assert all(d % 2 == 0 for _, d in G.degree())
    answers = [route_qp(R, pairing) for pairing in pairings]
    for answer in answers:
        close(answer[0], 2/3)
        close(answer[2], [2/3, 2/3])
        close(answer[3], [1/9, 1/9])
    delta = answers[1][1] - answers[0][1]
    close(answers[0][1] @ delta, -2/9)
    close(0.5 * delta @ delta, 2/9)

    R = nx.Graph([("a", "b"), ("b", "c"), ("c", "d"), ("d", "a"),
                  ("a", "u"), ("u", "b"), ("c", "w"), ("w", "d")])
    G = R.copy()
    G.add_edges_from(("v", t) for t in "abcd")
    assert G.number_of_nodes() == 7
    assert all(d % 2 == 0 for _, d in G.degree())
    answers = [route_qp(R, pairing) for pairing in pairings]
    close([a[0] for a in answers], [2/3, 1, 5/3])
    close(answers[0][3], [0, 0])
    delta = answers[1][1] - answers[0][1]
    close(answers[0][1] @ delta, -4/3)
    close(0.5 * delta @ delta, 5/3)
    close(answers[1][0] - answers[0][0], 1/3)

    # The full-cell boundary case used in the scalable obstruction.
    K4 = nx.complete_graph(list("abcd"))
    close(route_qp(K4, [("b", "a"), ("c", "a"), ("d", "a")])[0], 3/2)
    close(route_qp(K4, [("b", "c")])[0], 1/4)
    print("Exact small-example formulas independently confirmed by all-simple-route QPs.")


def loop_erase(walk):
    out = []
    for v in walk:
        if v in out:
            out = out[:out.index(v) + 1]
        else:
            out.append(v)
    return out


def check_coupled_descent():
    # Two equally likely compatible pairs in the K5 star-H example.
    # A coupling succeeds even though not every independent pair is compatible.
    outcomes = [(["a", "c", "b"], ["c", "a", "d"], ("a", "c")),
                (["a", "d", "b"], ["c", "b", "d"], ("d", "b"))]
    old, new, r = {}, {}, {}
    for Q1, Q2, (x, y) in outcomes:
        assert Q1[Q1.index(x) + 1] == y
        assert Q2[Q2.index(y) + 1] == x
        W1 = Q1[:Q1.index(x) + 1] + Q2[Q2.index(x) + 1:]
        W2 = Q2[:Q2.index(y) + 1] + Q1[Q1.index(y) + 1:]
        new_paths = [loop_erase(W1), loop_erase(W2)]
        assert new_paths == [["a", "d"], ["c", "b"]]
        for path in [Q1, Q2]:
            for e in edge_set(path):
                old[e] = old.get(e, F(0)) + F(1, 2)
        for path in new_paths:
            for e in edge_set(path):
                new[e] = new.get(e, F(0)) + F(1, 2)
        e = frozenset((x, y))
        r[e] = r.get(e, F(0)) + F(1, 2)
    all_edges = set(old) | set(new)
    for e in all_edges:
        assert new.get(e, 0) - old.get(e, 0) <= -2 * r.get(e, 0)
    gain = sum((old.get(e, 0)**2 - new.get(e, 0)**2 for e in all_edges), F(0))/2
    bound = 2 * sum((p * (old[e] - p) for e, p in r.items()), F(0))
    assert gain == bound == 1
    print("Exact-rational transport-coupled cancellation and paid gain verified.")


def check_three_tail_cancellation():
    H, R = nx.Graph(), nx.Graph()
    old_routes, new_routes = [], []
    for i in range(3):
        s, t = ("s", i), ("t", i)
        x, y = ("x", i), ("x", (i+1) % 3)
        H.add_edges_from([(s, "w"), ("w", t)])
        old_route = [s, x, y, t]
        new_route = [s, x, ("t", (i-1) % 3)]
        old_routes.append(old_route)
        new_routes.append(new_route)
        R.add_edges_from(zip(old_route, old_route[1:]))
    G = nx.compose(H, R)
    assert G.number_of_nodes() == 10
    assert all(d % 2 == 0 for _, d in G.degree())
    old_edges = [e for route in old_routes for e in edge_set(route)]
    new_edges = [e for route in new_routes for e in edge_set(route)]
    assert len(old_edges) == len(set(old_edges)) == 9
    assert len(new_edges) == len(set(new_edges)) == 6
    assert set(new_edges) < set(old_edges)
    assert all(R.has_edge(u, v) for p in new_routes for u, v in zip(p, p[1:]))
    gain = F(len(old_edges)-len(new_edges), 2)
    assert gain == F(3, 2)
    print("Even ten-vertex three-tail cancellation: exact gain 3/2, zero new H-cycles.")


def walecki(q, i):
    path = [i]
    for k in range(1, q):
        path.extend([(i-k) % (2*q), (i+k) % (2*q)])
    path.append((i-q) % (2*q))
    return path


def check_necklaces():
    for q in range(1, 15):
        paths = [walecki(q, i) for i in range(q)]
        used = set()
        for path in paths:
            assert len(set(path)) == len(path) == 2*q
            assert not used & edge_set(path)
            used |= edge_set(path)
        assert len(used) == q*(2*q-1)
        assert len({p[j] for p in paths for j in (0, -1)}) == 2*q
        for L in range(2, 8):
            whole = [[(j, v) for j in range(L) for v in p] for p in paths]
            H, G = nx.Graph(), nx.Graph()
            for p in whole:
                H.add_edges_from(zip(p, p[1:]))
                G.add_edges_from(zip(p, p[1:]))
                G.add_edge(p[0], p[-1])
            assert all(d == 2*q for _, d in G.degree())
            assert min(dict(H.degree()).values()) == 2*q-1
            assert H.number_of_edges() == q*(2*q*L-1)
            assert all(len(p) == G.number_of_nodes() for p in whole)
            connector_graph = nx.Graph([(u, v) for u, v in H.edges() if u[0] != v[0]])
            assert max(dict(connector_graph.degree()).values(), default=0) <= 1
            for r in range(q):
                R = nx.Graph()
                R.add_nodes_from(G)
                for p in whole[:r]:
                    R.add_edges_from(zip(p, p[1:]))
                    R.add_edge(p[0], p[-1])
                for p in whole[r:]:
                    R.add_edge(p[0], p[-1])
                for j in range(L-1):
                    cut = sum((u[0] <= j) != (v[0] <= j) for u, v in R.edges())
                    assert cut == q+r
                assert all(d in (2*r, 2*r+1) for _, d in R.degree())
    print("Walecki and necklace formulas verified: q=1..14, L=2..7, all r<q.")


def degree_share(G, C):
    return sum((F(C.degree(v), G.degree(v)) for v in C if C.degree(v)), F(0))


def check_harmonic_core_accounts():
    for m in (3, 5, 7):
        for L in (1, 3, 11):
            G, cores = nx.Graph(), []
            for j in range(L):
                C = nx.complete_graph([("center",)] + [(j, k) for k in range(m-1)])
                cores.append(C)
                G = nx.compose(G, C)
            assert all(d % 2 == 0 for _, d in G.degree())
            for C in cores:
                assert degree_share(G, C) == F(m-1) + F(1, L)
                assert degree_share(G, C) >= F(2*m, 3)
            assert sum((degree_share(G, C) for C in cores), F(0)) == G.number_of_nodes()
            assert L*m <= F(3, 2)*G.number_of_nodes()
    for q in range(1, 9):
        for L in range(2, 7):
            local = [walecki(q, i) for i in range(q)]
            whole = [[(j, v) for j in range(L) for v in p] for p in local]
            H, G = nx.Graph(), nx.Graph()
            for p in whole:
                H.add_edges_from(zip(p, p[1:]))
                G.add_edges_from(zip(p, p[1:]))
                G.add_edge(p[0], p[-1])
            assert degree_share(G, H) == 2*q*L-1
            new_paths = []
            used = set()
            for j in range(L):
                K = nx.Graph()
                for p in local:
                    piece = ([(j-1, p[-1])] if j else []) + [(j, v) for v in p]
                    assert not used & edge_set(piece)
                    used |= edge_set(piece)
                    new_paths.append(piece)
                    K.add_edges_from(zip(piece, piece[1:]))
                    budget = 1 + sum((F(1, G.degree(v)) for v in piece), F(0))
                    assert budget <= 2 + F(1, 2*q)
                C = K.subgraph([(j, v) for v in range(2*q)])
                assert degree_share(G, C) == 2*q-1
                assert C.number_of_edges() == q*(2*q-1)
                assert K.number_of_edges()-C.number_of_edges() == (q if j else 0)
            assert used == {frozenset(e) for e in H.edges()}
            assert len(new_paths) == q*L
            for v in G:
                assert sum((v == p[0]) + (v == p[-1]) for p in new_paths) <= 2
            for p in whole:
                C = nx.Graph(list(zip(p, p[1:])))
                a = 1 + sum((F(1, G.degree(v)) for v in p), F(0))
                assert a == 1+L
                assert degree_share(G, C) == 2*(a-1)-F(1, G.degree(p[0]))-F(1, G.degree(p[-1]))
    print("Harmonic edge-share accounts, overlapping windmills, and explicit necklace resegmentation verified.")


def check_inflated_cells():
    for q in (4, 8, 12):
        for f in (2, 4, 6):
            B = [("core", v) for v in range(2*q)]
            hubs = [("hub", v) for v in range(f)]
            H, R = nx.Graph(), nx.Graph()
            paths = []
            for i in range(q):
                p = [("leaf", i, 0)] + [("core", v) for v in walecki(q, i)] + [("leaf", i, 1)]
                paths.append(p)
                H.add_edges_from(zip(p, p[1:]))
            R.add_edges_from((z, v) for z in hubs for v in B)
            for i in range(0, q, 2):
                cell = [paths[i][0], paths[i][-1], paths[i+1][0], paths[i+1][-1]]
                R.add_edges_from(combinations(cell, 2))
                a = cell[0]
                R.add_edges_from((a, z) for z in hubs)
                for v in cell[1:]:
                    assert set(R.neighbors(v)) <= set(cell)
            G = nx.compose(H, R)
            assert not {frozenset(e) for e in H.edges()} & {frozenset(e) for e in R.edges()}
            assert G.number_of_nodes() == 4*q+f
            assert all(d % 2 == 0 for _, d in G.degree())
            assert nx.is_connected(R)
            assert all(nx.shortest_path_length(R, u, v) <= 3 for u, v in H.edges())
            closures = []
            for p in paths:
                assert R.has_edge(p[0], p[-1])
                assert sum((F(1, G.degree(v)) for v in p[1:-1]), F(0)) < 1
                assert 1 + sum((F(1, G.degree(v)) for v in p), F(0)) < F(5, 2)
                closures.append(frozenset((p[0], p[-1])))
            assert len(set(closures)) == q
            for r in range(1, q+1):
                K = nx.Graph()
                for p in paths[:r]:
                    K.add_edges_from(zip(p, p[1:]))
                assert K.number_of_nodes() == 2*q+2*r
                assert min(dict(K.degree()).values()) == 1
                assert K.subgraph(B).number_of_edges() == r*(2*q-1)
    print("Connected even inflated-cell obstructions and direct whole-path closures verified.")


def greedy_spanner(G):
    S = nx.Graph()
    S.add_nodes_from(G)
    for u, v in G.edges():
        if not nx.has_path(S, u, v) or nx.shortest_path_length(S, u, v) > 3:
            S.add_edge(u, v)
    return S


def check_local_spanners():
    rng = random.Random(784)
    for n in range(3, 10):
        for _ in range(10):
            G = nx.Graph()
            G.add_nodes_from(range(n))
            G.add_edges_from((u, v) for u, v in combinations(range(n), 2) if rng.random() < .7)
            unused = G.copy()
            layers = []
            for _ in range(3):
                S = greedy_spanner(unused)
                layers.append(S)
                unused.remove_edges_from(S.edges())
                for u, v in combinations(S, 2):
                    assert len(set(S.neighbors(u)) & set(S.neighbors(v))) <= 1
            for u, v in unused.edges():
                for S in layers:
                    assert nx.shortest_path_length(S, u, v) <= 3
            R = nx.compose_all(layers)
            for mask in range(1, 1 << n):
                X = [v for v in range(n) if mask >> v & 1]
                assert R.subgraph(X).number_of_edges() <= 3 * len(X)**1.5
    print("Greedy layered local reservoirs and all-subset hereditary bounds checked on small graphs.")


def refine_harmonic(G, paths):
    blocks = []
    for i, path in enumerate(paths):
        vertices, total = [], F(0)
        for v in path[1:-1]:
            vertices.append(v)
            total += F(1, G.degree(v))
            if total >= 1:
                assert total < F(3, 2)
                blocks.append((i, vertices))
                vertices, total = [], F(0)
    B = nx.Graph()
    left = []
    for k, (_, vertices) in enumerate(blocks):
        t = ("block", k)
        left.append(t)
        B.add_edges_from((t, ("vertex", v)) for v in vertices)
    matching = nx.algorithms.bipartite.maximum_matching(B, top_nodes=left) if blocks else {}
    assert len(matching)//2 == len(blocks)
    cuts = {i: set() for i in range(len(paths))}
    for k, (i, _) in enumerate(blocks):
        cuts[i].add(matching[("block", k)][1])
    out = []
    for i, path in enumerate(paths):
        positions = [0] + [j for j, v in enumerate(path) if v in cuts[i]] + [len(path)-1]
        out.extend(path[a:b+1] for a, b in zip(positions, positions[1:]))
    assert len(out) == len(paths)+len(blocks)
    assert 2*len(blocks) <= G.number_of_nodes()
    assert all(sum((F(1, G.degree(v)) for v in path), F(0)) < 3 for path in out)
    assert sum(1 + sum((F(1, G.degree(v)) for v in path), F(0)) for path in out) <= len(out)+G.number_of_nodes()
    for v in G:
        old_ends = sum((v == p[0]) + (v == p[-1]) for p in paths)
        new_ends = sum((v == p[0]) + (v == p[-1]) for p in out)
        assert new_ends <= old_ends+2
    return len(blocks)


def check_harmonic_segmentation():
    random.seed(1484)
    runs, cuts = 0, 0
    for n in range(3, 80):
        for _ in range(15):
            G = nx.cycle_graph(n)
            for _ in range(n//2):
                vertices = random.sample(range(n), random.randint(3, min(n, 9)))
                edges = [tuple(sorted(e)) for e in zip(vertices, vertices[1:]+vertices[:1])]
                if all(not G.has_edge(*e) for e in edges):
                    G.add_edges_from(edges)
            unused = G.copy()
            paths = []
            while unused.number_of_edges():
                v = random.choice([v for v, d in unused.degree if d])
                path = [v]
                while True:
                    neighbors = [w for w in unused.neighbors(path[-1]) if w not in path]
                    if not neighbors:
                        break
                    w = random.choice(neighbors)
                    unused.remove_edge(path[-1], w)
                    path.append(w)
                paths.append(path)
            assert all(G.degree(v) % 2 == 0 for v in G)
            cuts += refine_harmonic(G, paths)
            runs += 1
    assert runs == 1155 and cuts == 14219, (runs, cuts)
    print(f"Exact-rational harmonic segmentation: {runs} even graphs, {cuts} distinct-representative cuts.")


def main():
    spec = Path(__file__).with_name("Spec.lean")
    assert sha256(spec.read_bytes()).hexdigest() == SPEC_SHA256
    check_small_qps()
    check_coupled_descent()
    check_three_tail_cancellation()
    check_necklaces()
    check_harmonic_core_accounts()
    check_inflated_cells()
    check_local_spanners()
    check_harmonic_segmentation()
    assert sha256(spec.read_bytes()).hexdigest() == SPEC_SHA256
    print("All checks passed; Spec.lean SHA-256 unchanged.")


if __name__ == "__main__":
    main()
