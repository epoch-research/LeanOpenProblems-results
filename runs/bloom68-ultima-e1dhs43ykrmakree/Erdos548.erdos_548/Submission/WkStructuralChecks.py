#!/usr/bin/env python3
"""Exact finite checks for WkStructuralFindings.md.

These checks validate explicit certificates and small instances, not the
unrestricted W_k conjecture.  All containment checks are NON-INDUCED.
Requires Python 3 and NetworkX.  Does not write Spec.lean.
"""
from functools import lru_cache
import hashlib
from pathlib import Path

import networkx as nx

SPEC_HASH = "674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103"


def wk_order(G, k):
    """Return a witnessing activation order, or None if a resistant set remains."""
    remaining = set(G)
    active = set()
    order = []
    while remaining:
        v = next((v for v in remaining
                  if G.degree(v) + len(set(G[v]) & active) >= k), None)
        if v is None:
            return None
        remaining.remove(v)
        active.add(v)
        order.append(v)
    return order


def order_scores(G, order):
    assert len(order) == len(G) and set(order) == set(G)
    earlier = set()
    scores = []
    for v in order:
        scores.append(G.degree(v) + len(set(G[v]) & earlier))
        earlier.add(v)
    return scores


def exact_w_value(G):
    """Directly evaluate min_{nonempty X} max_{v in X}(2d(v)-d_X(v))."""
    vertices = list(G)
    index = {v: i for i, v in enumerate(vertices)}
    masks = [sum(1 << index[w] for w in G[v]) for v in vertices]
    degrees = [m.bit_count() for m in masks]
    return min(max(2 * degrees[i] - (masks[i] & X).bit_count()
                   for i in range(len(vertices)) if X >> i & 1)
               for X in range(1, 1 << len(vertices)))


@lru_cache(None)
def trees(n):
    if n == 1:
        return (nx.empty_graph(1),)
    return tuple(nx.nonisomorphic_trees(n))


def verify_injection(T, G, phi):
    assert set(phi) == set(T)
    assert len(set(phi.values())) == len(T)
    assert set(phi.values()) <= set(G)
    assert all(G.has_edge(phi[u], phi[v]) for u, v in T.edges())


def check_order_and_deletion(atlas):
    comparisons = 0
    tails = 0
    for G in atlas:
        if not G:
            continue
        w = exact_w_value(G)
        for k in range(len(G) + 1):
            order = wk_order(G, k)
            assert (order is not None) == (k <= w)
            comparisons += 1
        order = wk_order(G, w)
        assert min(order_scores(G, order)) >= w
        assert sum(order_scores(G, order)) == 3 * G.number_of_edges()
        for r in range(min(w, len(G) - 1) + 1):
            prefix = order[:len(G) - r]
            H = G.subgraph(prefix)
            assert min(order_scores(H, prefix)) >= w - r
            assert wk_order(H, w - r) is not None
            tails += 1
        if w >= 1 and len(G) >= 2:
            z = order[-1]
            H = G.subgraph(order[:-1])
            S = set(G[z])
            scores = order_scores(H, order[:-1])
            assert 2 * len(S) >= w
            for v, score in zip(order[:-1], scores):
                assert score >= w - int(v in S)
    print(f"Ordering/subset equivalence: {comparisons} atlas graph/parameter checks; "
          f"{tails} tail-deletion certificates.")


def partitions(n, lower=1):
    if n == 0:
        yield ()
    else:
        for first in range(lower, n + 1):
            for rest in partitions(n - first, first):
                yield (first,) + rest


def check_multipartite():
    hosts = 0
    capacity_checks = 0
    for n in range(1, 18):
        for sizes in partitions(n):
            hosts += 1
            P = 0
            M = 0
            sums = {0}
            for c in sizes:
                M = max(M, c - P)
                P += c
                sums |= {s + c for s in sums}
            sorted_sums = sorted(sums)
            assert max(y - x for x, y in zip(sorted_sums, sorted_sums[1:])) == M
            w = n - M
            G = nx.complete_multipartite_graph(*sizes)
            order = wk_order(G, w)
            assert order is not None and min(order_scores(G, order)) >= w
            assert wk_order(G, w + 1) is None
            for k in range(1, w + 1):
                t = n - k
                # Check the interval-cover statement itself, not just a tree test.
                covered = {s + j for s in sums for j in range(t)}
                assert covered == set(range(n + t))
                for a in range(1, k + 1):
                    b = k + 1 - a
                    assert any(a <= s <= n - b for s in sums)
                    capacity_checks += 1
    print(f"Multipartite theorem: {hosts} integer partitions through n=17; "
          f"{capacity_checks} bipartition-capacity checks.")


def check_independent_deletion():
    tree_count = 0
    choices = 0
    for n in range(2, 12):
        for T in trees(n):
            tree_count += 1
            k = n - 1
            color = nx.bipartite.color(T)
            for side in (0, 1):
                A = [v for v in T if color[v] == side]
                if 2 * len(A) > len(T):
                    continue
                A.sort(key=lambda v: T.degree(v), reverse=True)
                for r in range(1, len(A)):
                    U = set(A[:r])
                    degree_sum = sum(T.degree(v) for v in U)
                    F = T.subgraph(set(T) - U)
                    assert not any(T.has_edge(u, v) for u in U for v in U)
                    assert degree_sum >= 2 * r
                    assert F.number_of_edges() == k - degree_sum <= k - 2 * r
                    assert len(F) == k + 1 - r <= k
                    assert nx.is_forest(F)
                    choices += 1
    print(f"Independent deletion lemma: {tree_count} unlabeled trees through 11 vertices; "
          f"{choices} choices of smaller color class and r.")


def check_forest_theorem_small(atlas):
    forests = [F for F in atlas if len(F) and nx.is_forest(F)]
    checks = 0
    for G in atlas:
        if not G:
            continue
        delta = min(dict(G.degree()).values())
        for F in forests:
            if len(F) <= len(G) and F.number_of_edges() <= delta:
                assert nx.algorithms.isomorphism.GraphMatcher(G, F).subgraph_is_monomorphic()
                checks += 1
    print(f"Cited forest theorem: {checks} qualifying graph-atlas forest/host checks (non-induced).")


def check_interface_small(atlas):
    checks = 0
    for H in atlas:
        if not 2 <= len(H) <= 5:
            continue
        delta = min(dict(H.degree()).values())
        for r in range(1, 4):
            G = nx.convert_node_labels_to_integers(H)
            S = list(range(len(H), len(H) + r))
            G.add_nodes_from(S)
            G.add_edges_from((s, h) for s in S for h in H)
            for k in range(2, len(H) + 1):
                if delta < k - 2 * r:
                    continue
                certificate = S + list(H)
                assert min(order_scores(G, certificate)) >= k
                for T in trees(k + 1):
                    assert nx.algorithms.isomorphism.GraphMatcher(G, T).subgraph_is_monomorphic()
                    checks += 1
    print(f"Independent-interface theorem: {checks} exact small non-induced embedding checks.")


def check_end_block_capacity():
    checks = 0
    for a in range(2, 12):
        for b in range(2, 12):
            for k in range(3, 11):
                if 2 * min(a, b) < k or max(a, b + 1) < k:
                    continue
                for T in trees(k + 1):
                    if max(dict(T.degree()).values()) == k:
                        continue  # The star is supplied by the whole graph's degree-k vertex.
                    color = nx.bipartite.color(T)
                    p = sum(c == 0 for c in color.values())
                    q = len(T) - p
                    assert (p <= a and q <= b) or (q <= a and p <= b)
                    checks += 1
    print(f"Complete-bipartite end-block lemma: {checks} nonstar capacity checks.")


def two_wing_host(k):
    assert k >= 4 and k % 2 == 0
    r = k // 2
    z = ("z", 0, 0)
    A = [[("a", i, j) for j in range(r)] for i in range(2)]
    B = [[("b", i, j) for j in range(k - 2)] for i in range(2)]
    G = nx.Graph()
    G.add_node(z)
    for i in range(2):
        G.add_edges_from((a, b) for a in A[i] for b in B[i] + [z])
    order = [z] + A[0] + A[1] + B[0] + B[1]
    assert order_scores(G, order) == [k] * len(G)
    assert [v for v in G if G.degree(v) >= k] == [z]
    assert len(G) == 3 * k - 3
    assert G.number_of_edges() == k * (k - 1)
    assert 3 * G.number_of_edges() == k * len(G)
    return G, z, A, B


def check_maximum_root_obstruction():
    G, z, A, B = two_wing_host(14)
    h = [("h", i) for i in range(4)]
    T = nx.Graph()
    for i in range(1, 4):
        c = ("c", i)
        T.add_edges_from([(h[0], c), (c, h[i])])
        for j in range(3 if i < 3 else 2):
            T.add_edge(h[i], ("leaf", i, j))
    TA = set(h)
    TB = set(T) - TA
    assert nx.is_tree(T) and T.number_of_edges() == 14
    assert (len(TA), len(TB)) == (4, 11)
    maximum_roots = [v for v in T if T.degree(v) == 4]
    assert set(maximum_roots) == {h[1], h[2]}
    assert max(dict(T.degree()).values()) == 4
    for root in maximum_roots:
        R = T.subgraph(set(T) - {root})
        nontrivial = [C for C in nx.connected_components(R) if len(C) > 1]
        assert len(nontrivial) == 1
        C = nontrivial[0]
        assert (len(C & TA), len(C & TB)) == (3, 8)
        connector = next(v for v in T[root] if v in C)
        assert connector in TB
        # If root -> z, connector must map into some A[i].  Connectivity
        # confines C to that wing, so all eight vertices of C & TB would
        # have to map into its seven-vertex part A[i].
        assert len(C & TB) > len(A[0]) == len(A[1])
    phi = dict(zip(h, A[0]))
    phi.update(zip(sorted(TB), B[0]))
    verify_injection(T, G, phi)
    assert z not in phi.values()
    print("Maximum-root obstruction: W_14 host n=39,m=182, unique seed; "
          "both maximum-degree tree roots excluded by 8>7; explicit unrooted embedding verified.")


def check_c6_root_obstruction():
    sizes = (6, 6, 3, 6, 6, 1)
    parts = [[(i, j) for j in range(c)] for i, c in enumerate(sizes)]
    G = nx.Graph()
    for i in range(6):
        G.add_edges_from((a, b) for a in parts[i] for b in parts[(i + 1) % 6])
    assert len(G) == 28 and G.number_of_edges() == 120
    assert nx.is_biconnected(G)
    assert [G.degree(P[0]) for P in parts] == [7, 9, 12, 9, 7, 12]
    order = sum((parts[i] for i in (2, 5, 1, 3, 0, 4)), [])
    assert min(order_scores(G, order)) >= 12
    T = nx.Graph([("ell", "u"), ("u", "c"), ("c", "z")])
    T.add_edges_from(("z", f"x{i}") for i in range(9))
    assert nx.is_tree(T) and T.number_of_edges() == 12 and T.degree("z") == 10
    f = parts[5][0]
    dist = nx.single_source_shortest_path_length(G, f, cutoff=2)
    distance_two = {v for v, d in dist.items() if d == 2}
    assert distance_two == set(parts[1] + parts[3])
    assert max(G.degree(v) for v in distance_two) == 9 < T.degree("z")
    # T is bipartite and u,z are distinct and in the same color class;
    # an image of z at distance <= 2 from f must therefore be at distance 2.
    phi = {"z": parts[2][0], "c": parts[1][0], "u": parts[0][0], "ell": f}
    phi.update(zip((f"x{i}" for i in range(9)), parts[1][1:] + parts[3][:4]))
    verify_injection(T, G, phi)
    print("C6 blow-up root obstruction: W_12 certificate, distance-two degree obstruction, "
          "and explicit unrooted embedding verified.")


def check_endpoint_potential(atlas):
    hamiltonian_hosts = 0
    path_checks = 0
    for H in atlas:
        if not H:
            continue
        n = len(H)
        vertices = list(H)
        index = {v: i for i, v in enumerate(vertices)}
        neighbors = [sum(1 << index[w] for w in H[v]) for v in vertices]
        # endpoints[M] records all possible ends of paths spanning exactly M.
        endpoints = [0] * (1 << n)
        for M in range(1, 1 << n):
            if M & (M - 1) == 0:
                endpoints[M] = M
            else:
                for v in range(n):
                    if M >> v & 1 and endpoints[M ^ (1 << v)] & neighbors[v]:
                        endpoints[M] |= 1 << v
        S = endpoints[-1]
        if S:
            hamiltonian_hosts += 1
            for v in range(n):
                if S >> v & 1:
                    assert 2 * neighbors[v].bit_count() - (neighbors[v] & S).bit_count() <= n - 1
        longest = max(M.bit_count() for M, ends in enumerate(endpoints) if ends) - 1
        assert longest >= exact_w_value(H)
        path_checks += 1

    # A counterexample to replacing paths by arbitrary spanning trees and
    # replacing endpoint support by the union of all leaf supports.
    H = nx.Graph([(0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
                  (1, 2), (2, 3), (2, 5), (3, 4), (4, 6)])
    F = nx.Graph([(1, 0), (1, 2), (1, 3), (0, 4), (4, 5), (4, 6)])
    leaves = {v for v in F if F.degree(v) == 1}
    S = set()
    copies = 0
    for phi in nx.algorithms.isomorphism.GraphMatcher(H, F).subgraph_monomorphisms_iter():
        copies += 1
        S.update(v for v in H if phi[v] in leaves)
    assert S == {0, 1, 3, 5, 6} and copies == 16
    assert 2 * H.degree(0) - len(set(H[0]) & S) == 7 > F.number_of_edges() == 6
    print(f"Global path endpoint lemma: {hamiltonian_hosts} Hamiltonian atlas hosts; "
          f"{path_checks} longest-path/W checks. All-leaf generalization fails on 16 verified spanning copies.")


def check_weak_tail_input_failure():
    H = nx.complete_bipartite_graph(3, 5)
    S = {3, 4, 5}
    assert wk_order(H, 5) is not None and len(S) == 3
    G = H.copy()
    z = 8
    G.add_edges_from((z, v) for v in S)
    assert max(dict(G.degree()).values()) == 5
    assert wk_order(G, 6) is None
    print("Weakened tail-input counterexample: W_5 plus |S|=3 does not force a 6-star after adjoining z.")


def main():
    spec = Path(__file__).with_name("Spec.lean")
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_HASH
    atlas = nx.graph_atlas_g()
    check_order_and_deletion(atlas)
    check_multipartite()
    check_independent_deletion()
    check_forest_theorem_small(atlas)
    check_interface_small(atlas)
    check_end_block_capacity()
    check_maximum_root_obstruction()
    check_c6_root_obstruction()
    check_endpoint_potential(atlas)
    check_weak_tail_input_failure()
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_HASH
    print("All checks passed. Spec.lean is unchanged. The unrestricted W_k implication is NOT proved.")


if __name__ == "__main__":
    main()
