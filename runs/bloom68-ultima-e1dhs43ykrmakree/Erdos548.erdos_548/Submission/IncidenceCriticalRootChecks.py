#!/usr/bin/env python3
"""Exact checks for IncidenceCriticalRootFindings.md.

The new results are obstruction/certificate statements, not an Erdos--Sos
proof. No search success is used as evidence for an unrestricted lemma.
All embeddings here are injective homomorphisms, not induced embeddings.
"""
from fractions import Fraction
from pathlib import Path
import hashlib
import itertools
import networkx as nx

SPEC_HASH = "674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103"


def circuit_parameters(r):
    assert r >= 2
    a, b, t = r + 1, r * r, r + 1
    n = t * (a + b) + 1
    m = t * a * (b + 1)
    assert m == r * n + 1
    assert t * a > b + 1 > a
    return a, b, t, n, m


def host(r):
    a, b, t, n, m = circuit_parameters(r)
    s = ("s", 0, 0)
    A = [[("A", i, j) for j in range(a)] for i in range(t)]
    B = [[("B", i, j) for j in range(b)] for i in range(t)]
    G = nx.Graph()
    G.add_node(s)
    for i in range(t):
        G.add_edges_from(itertools.product(A[i], B[i]))
        G.add_edges_from((s, v) for v in A[i])
    assert len(G) == n and G.number_of_edges() == m
    assert G.degree(s) == t * a
    assert all(G.degree(v) == b + 1 for row in A for v in row)
    assert all(G.degree(v) == a for row in B for v in row)
    assert [v for v in G if G.degree(v) == max(dict(G.degree()).values())] == [s]
    assert nx.is_connected(G) and nx.is_bipartite(G)
    return G, s, A, B


def check_all_subset_types():
    """Counts classify every subset of every wing under its twin symmetries.

    Separability then evaluates the maximum over all proper subsets of G:
    with s present, at least one wing must be nonfull. No sampling of vertex
    subsets and no inference from average/minimum degree is involved.
    """
    count = 0
    for r in range(2, 61):
        a, b, t, n, m = circuit_parameters(r)
        with_s = []
        nonfull_with_s = []
        without_s = []
        for x in range(a + 1):
            for y in range(b + 1):
                # The first score includes edges from the selected A vertices
                # to s, but does not yet charge the single shared vertex s.
                score = x * y + x - r * (x + y)
                with_s.append(score)
                if (x, y) != (a, b):
                    nonfull_with_s.append(score)
                without_s.append(x * y - r * (x + y))
                count += 1
        assert max(with_s) == 1
        assert with_s.count(1) == 1
        assert max(nonfull_with_s) == 0
        assert max(without_s) == 0
        assert -r + t * max(with_s) == 1
        assert -r + (t - 1) * max(with_s) + max(nonfull_with_s) == 0
        assert t * max(without_s) == 0
    print(f"Critical-host all-subset certificates: r=2..60, {count} exact wing types.")


def verify_injection(T, G, phi):
    assert set(phi) == set(T)
    assert len(set(phi.values())) == len(T)
    assert set(phi.values()) <= set(G)
    assert all(G.has_edge(phi[x], phi[y]) for x, y in T.edges())


def branch_profile(T, u):
    """(odd-distance count, positive-even-distance count) in each branch."""
    dist = nx.single_source_shortest_path_length(T, u)
    F = T.subgraph(set(T) - {u})
    return [(sum(dist[v] % 2 for v in C),
             sum(dist[v] % 2 == 0 for v in C))
            for C in nx.connected_components(F)]


def apex_feasible(T, u, a, b, t):
    # Each connected branch stays in one component of G-s; its bipartite
    # orientation is forced. With one wing per branch, these tests are both
    # necessary and sufficient, not just a degree relaxation.
    assert t >= T.degree(u)
    return all(x <= a and y <= b for x, y in branch_profile(T, u))


def construct_apex_embedding(T, u, G, s, A, B):
    assert apex_feasible(T, u, len(A[0]), len(B[0]), len(A))
    dist = nx.single_source_shortest_path_length(T, u)
    phi = {u: s}
    for i, C in enumerate(nx.connected_components(T.subgraph(set(T) - {u}))):
        odds = sorted((v for v in C if dist[v] % 2), key=repr)
        evens = sorted((v for v in C if dist[v] % 2 == 0), key=repr)
        phi.update(zip(odds, A[i]))
        phi.update(zip(evens, B[i]))
    verify_injection(T, G, phi)
    assert phi[u] == s
    return phi


def degree_four_tree(r):
    """A (2r+1)-edge tree, r>=9, with a unique degree-four vertex u.

    Start with r-4 X vertices linked in a path by r-5 Y vertices; add
    seven Y leaves, two at each X end and one at three internal X vertices.
    Attach u to one of those leaves, then add three leaves at u.
    """
    assert r >= 9
    X = [("x", i) for i in range(r - 4)]
    Y = [("y", i) for i in range(r - 5)]
    T = nx.Graph()
    for i, y in enumerate(Y):
        T.add_edges_from([(X[i], y), (y, X[i + 1])])
    parents = [X[0], X[0], X[-1], X[-1], X[1], X[2], X[3]]
    leaves = [("ell", i) for i in range(7)]
    T.add_edges_from(zip(parents, leaves))
    R = set(T)
    u = ("u", 0)
    T.add_edge(u, leaves[0])
    T.add_edges_from((u, ("u_leaf", j)) for j in range(3))
    assert nx.is_tree(T)
    assert T.number_of_edges() == 2 * r + 1
    assert len(T) == 2 * r + 2
    assert T.degree(u) == 4
    assert all(T.degree(v) <= 3 for v in T if v != u)
    color = nx.bipartite.color(T)
    small = {v for v in T if color[v] == color[u]}
    large = set(T) - small
    assert len(small) == r - 3 and len(large) == r + 5
    assert len(R & small) == r - 4 and len(R & large) == r + 2
    assert sorted(branch_profile(T, u)) == [(1, 0)] * 3 + [(r + 2, r - 4)]
    return T, u, small, large


def three_hub_tree():
    T = nx.Graph()
    z = ("z", 0)
    hubs = [("h", i) for i in range(3)]
    for i, h in enumerate(hubs):
        T.add_edge(z, h)
        T.add_edges_from((h, ("leaf", i, j)) for j in range(4))
    assert nx.is_tree(T) and T.number_of_edges() == 15
    assert max(dict(T.degree()).values()) == 5
    return T, z, set(hubs)


def check_weight_certificate(G, s, A, B):
    """Independent rational incidence certificate, checked edge by edge."""
    a, b, t, n = len(A[0]), len(B[0]), len(A), len(G)
    load = {v: Fraction(0) for v in G}
    seen = set()
    for i in range(t):
        for x in A[i]:
            w_s = Fraction(b + 1, n)
            assert 0 <= w_s <= 1
            load[s] += w_s
            load[x] += 1 - w_s
            seen.add(frozenset((s, x)))
            for y in B[i]:
                w_y = Fraction(t * (b + 1), n)
                assert 0 <= w_y <= 1
                load[y] += w_y
                load[x] += 1 - w_y
                seen.add(frozenset((x, y)))
    assert seen == {frozenset(e) for e in G.edges()}
    common = Fraction(G.number_of_edges(), n)
    assert set(load.values()) == {common}
    return common


def check_root_obstructions():
    # The proof is uniform in r; all root branch-capacity claims for the
    # bounded-degree family are independently evaluated here.
    for r in range(9, 101):
        T, u, small, large = degree_four_tree(r)
        a, b, t, _, _ = circuit_parameters(r)
        assert not apex_feasible(T, u, a, b, t)
        assert all(apex_feasible(T, v, a, b, t) for v in large)
        assert len(small) <= a and len(large) <= b
    print("Unique-maximum-degree-four obstruction and alternative roots: r=9..100.")

    r = 9
    G, s, A, B = host(r)
    T, u, small, large = degree_four_tree(r)
    # An unrooted embedding entirely within one wing is explicit.
    phi = dict(zip(sorted(small, key=repr), A[0]))
    phi.update(zip(sorted(large, key=repr), B[0]))
    verify_injection(T, G, phi)
    assert s not in phi.values()
    # In fact a degree-two tree vertex can occupy s; it is the choice of
    # the unique maximum-degree tree vertex that is impossible.
    v = next(v for v in large if T.degree(v) == 2)
    construct_apex_embedding(T, v, G, s, A, B)
    load = check_weight_certificate(G, s, A, B)
    assert load == Fraction(8200, 911) > 9
    print(f"k=19 graph: n={len(G)}, m={G.number_of_edges()}, "
          f"d(s)={G.degree(s)}, constant load={load}; two injections verified.")

    # One fixed tree has disjoint permissible roles at maximum-degree host
    # vertices in two genuine incidence-minimal (+1) hosts.
    T, z, hubs = three_hub_tree()
    G1, s1, A1, B1 = host(7)
    allowed = {u for u in T if apex_feasible(T, u, 8, 49, 8)}
    assert allowed == set(T) - hubs
    for u in allowed:
        construct_apex_embedding(T, u, G1, s1, A1, B1)
    assert check_weight_certificate(G1, s1, A1, B1) == Fraction(3200, 457)

    G2 = nx.complete_bipartite_graph(8, 57)
    assert len(G2) == 65 and G2.number_of_edges() == 456 == 7 * 65 + 1
    for x in range(9):
        for y in range(58):
            if (x, y) != (8, 57):
                assert x * y <= 7 * (x + y)
    s2 = 0
    assert G2.degree(s2) == max(dict(G2.degree()).values()) == 57
    for u in hubs:
        ordered_hubs = [u] + sorted(hubs - {u}, key=repr)
        phi = dict(zip(ordered_hubs, range(8)))
        phi.update(zip(sorted(set(T) - hubs, key=repr), range(8, 65)))
        assert phi[u] == s2
        verify_injection(T, G2, phi)
    assert len(set(T) - hubs) == 13 > 8  # Forced-color obstruction for every other role.
    print("k=15 disjoint role supports: 13 roles versus 3 roles; all allowed roles constructed.")


def check_boundary_identity():
    cases = 0
    connected = 0
    for n in range(2, 11):
        for T in nx.nonisomorphic_trees(n):
            V = list(T)
            k = n - 1
            for mask in range(1, (1 << n) - 1):
                U = {V[i] for i in range(n) if (mask >> i) & 1}
                F = T.subgraph(set(T) - U)
                D = T.subgraph(U)
                components = list(nx.connected_components(F))
                eU = D.number_of_edges()
                degsum = sum(T.degree(v) for v in U)
                boundary = [sum(T.has_edge(x, u) for x in C for u in U)
                            for C in components]
                assert all(b >= 1 for b in boundary)
                assert F.number_of_edges() == k - degsum + eU
                assert sum(b - 1 for b in boundary) == nx.number_connected_components(D) - 1
                if nx.is_connected(D):
                    b = sum(boundary)
                    assert all(x == 1 for x in boundary)
                    assert F.number_of_edges() == k - len(U) + 1 - b
                    assert ((F.number_of_edges() <= (k + 1) // 2 - len(U))
                            == (b >= k // 2 + 1))
                    guaranteed_delta = max(0, (k + 1) // 2 - len(U))
                    assert ((F.number_of_edges() <= guaranteed_delta)
                            == (F.number_of_edges() == 0 or b >= k // 2 + 1))
                    leaves = sum(T.degree(v) == 1 for v in T)
                    assert b <= leaves
                    if leaves <= k // 2 and F.number_of_edges() <= guaranteed_delta:
                        assert F.number_of_edges() == 0
                        assert all(T.degree(v) == 1 for v in F)
                    connected += 1
                cases += 1
    print(f"Boundary and residual-budget identities: {cases} tree/deletion pairs; "
          f"{connected} connected deletions.")


def main():
    spec = Path(__file__).with_name("Spec.lean")
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_HASH
    check_all_subset_types()
    check_root_obstructions()
    check_boundary_identity()
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_HASH
    print("PASS; Spec.lean unchanged. These are certified obstructions, not an ES proof.")


if __name__ == "__main__":
    main()
