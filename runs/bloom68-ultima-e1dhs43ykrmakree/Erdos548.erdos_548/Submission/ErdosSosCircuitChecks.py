#!/usr/bin/env python3
"""Exact finite checks for ErdosSosCircuitFindings.md.

Uses only Python's standard library and NetworkX. Containment is non-induced.
The mathematical proofs are in the accompanying document; these finite checks
are not asserted to prove unrestricted Erdos--Sos.
"""
from collections import Counter
from itertools import combinations
from pathlib import Path
import hashlib
import json
import random
import networkx as nx

SPEC_HASH = "674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103"


def edge_counts(G):
    """All induced edge counts, including parallel-edge multiplicities."""
    vertices = list(G)
    index = {v: i for i, v in enumerate(vertices)}
    counts = [0] * (1 << len(vertices))
    if not G.is_multigraph():
        masks = [sum(1 << index[w] for w in G.neighbors(v)) for v in vertices]
        for s in range(1, len(counts)):
            bit = s & -s
            v = bit.bit_length() - 1
            rest = s ^ bit
            counts[s] = counts[rest] + (masks[v] & rest).bit_count()
    else:
        neighbors = [
            [(index[w], G.number_of_edges(v, w)) for w in G.neighbors(v)]
            for v in vertices
        ]
        for s in range(1, len(counts)):
            bit = s & -s
            v = bit.bit_length() - 1
            rest = s ^ bit
            counts[s] = counts[rest] + sum(m for w, m in neighbors[v] if rest >> w & 1)
    return vertices, counts


def is_circuit(G, r):
    n = len(G)
    if not n or G.number_of_edges() != r * n + 1:
        return False
    _, counts = edge_counts(G)
    return all(counts[s] <= r * s.bit_count() for s in range(len(counts) - 1))


def is_spanning_map(P):
    """Each component is unicyclic, with isolated vertices counted as failures."""
    return all(P.subgraph(C).number_of_edges() == len(C) for C in nx.connected_components(P))


def quota_orientation(G, r, root):
    edges = list(G.edges())
    B = nx.Graph()
    left = [("edge", i) for i in range(len(edges))]
    slots = [("slot", v, j) for v in G for j in range(r + (v == root))]
    B.add_nodes_from(left, bipartite=0)
    B.add_nodes_from(slots, bipartite=1)
    for i, edge in enumerate(edges):
        for v in edge:
            for j in range(r + (v == root)):
                B.add_edge(("edge", i), ("slot", v, j))
    matching = nx.algorithms.bipartite.maximum_matching(B, top_nodes=left)
    assert all(e in matching for e in left)
    D = nx.DiGraph()
    D.add_nodes_from(G)
    for i, (u, v) in enumerate(edges):
        tail = matching[("edge", i)][1]
        D.add_edge(tail, v if tail == u else u)
    assert all(D.out_degree(v) == r + (v == root) for v in G)
    return D


def decompose_avoiding(G, r, F):
    """One red map avoids F; r-1 other maps and an extra edge complete G.

    Returns None exactly when the edge/slot matching instance has no solution.
    """
    F = {frozenset(e) for e in F}
    edges = list(G.edges())
    B = nx.Graph()
    left = [("edge", i) for i in range(len(edges))]
    slots = [("slot", c, v) for c in range(r) for v in G]
    extra = ("extra",)
    B.add_nodes_from(left, bipartite=0)
    B.add_nodes_from(slots + [extra], bipartite=1)
    for i, edge in enumerate(edges):
        B.add_edge(("edge", i), extra)
        for v in edge:
            for c in range(r):
                if c != 0 or frozenset(edge) not in F:
                    B.add_edge(("edge", i), ("slot", c, v))
    matching = nx.algorithms.bipartite.maximum_matching(B, top_nodes=left)
    if not all(e in matching for e in left):
        return None
    maps = [nx.Graph() for _ in range(r)]
    for P in maps:
        P.add_nodes_from(G)
    extra_edge = None
    for i, edge in enumerate(edges):
        slot = matching[("edge", i)]
        if slot == extra:
            extra_edge = edge
        else:
            maps[slot[1]].add_edge(*edge)
    assert extra_edge is not None
    assert all(P.number_of_edges() == len(G) and is_spanning_map(P) for P in maps)
    assert all(frozenset(e) not in F for e in maps[0].edges())
    all_edges = [frozenset(e) for P in maps for e in P.edges()] + [frozenset(extra_edge)]
    assert len(all_edges) == len(set(all_edges)) == G.number_of_edges()
    assert set(all_edges) == {frozenset(e) for e in G.edges()}
    return maps, extra_edge


def sharp_forbidden_example(r):
    a = 2 * r + 1
    G = nx.complete_graph(a)
    u, v = a, a + 1
    G.add_edge(u, v)
    Nu = set(range(r))
    Nv = {0} | set(range(r, 2 * r - 1))
    assert len(Nu) == len(Nv) == r and len(Nu & Nv) == 1
    F = [(u, w) for w in Nu] + [(v, w) for w in Nv]
    G.add_edges_from(F)
    return G, F


def blocked_star_decomposition(r):
    """C_r = map P + spanning C_{r-1}, but no smaller star extends."""
    a, b, u, v = 0, 1, 2 * r, 2 * r + 1
    cs = list(range(2, r + 1))
    ds = list(range(r + 1, 2 * r))
    G = nx.complete_graph(2 * r + 2)
    G.remove_edges_from([(a, b)] + list(zip(cs, ds)))
    P = nx.Graph()
    P.add_nodes_from(G)
    P.add_edges_from([(u, a), (a, v), (v, b), (b, u)])
    P.add_edges_from(zip([u] + cs[:-1], cs))
    P.add_edges_from(zip([v] + ds[:-1], ds))
    H = G.copy()
    H.remove_edges_from(P.edges())
    return G, P, H, (u, v), (cs[-1], ds[-1])


def run_checks():
    spec = Path(__file__).with_name("Spec.lean")
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_HASH
    stats = Counter()
    atlas_circuits = []
    for G in nx.graph_atlas_g():
        n = len(G)
        if not n:
            continue
        for r in (1, 2):
            if is_circuit(G, r):
                atlas_circuits.append((G, r))
                stats[f"atlas_r{r}_circuits"] += 1

    for G, r in atlas_circuits:
        vertices, counts = edge_counts(G)
        n = len(G)
        assert min(dict(G.degree()).values()) >= r + 1
        assert max(dict(G.degree()).values()) >= 2 * r + 1
        assert n >= 2 * r + 2
        for mask in range(1 << n):
            U = {vertices[i] for i in range(n) if mask >> i & 1}
            remaining = G.subgraph(set(G) - U)
            c = nx.number_connected_components(remaining)
            assert c + counts[mask] <= r * len(U) + 1
            stats["component_inequalities"] += 1
        for root in G:
            D = quota_orientation(G, r, root)
            assert len(nx.descendants(D, root)) == n - 1
            A = nx.bfs_tree(D, root).to_undirected()
            assert nx.is_tree(A) and len(A) == n
            assert max(dict(A.degree()).values()) <= r + 1
            tight_avoiding_root = any(
                mask and not (mask >> vertices.index(root) & 1)
                and counts[mask] == r * mask.bit_count()
                for mask in range((1 << n) - 1)
            )
            assert nx.is_strongly_connected(D) == (not tight_avoiding_root)
            stats["rooted_orientations"] += 1
            for new_root in G:
                path = nx.shortest_path(D, root, new_root)
                moved = D.copy()
                for u, v in zip(path, path[1:]):
                    moved.remove_edge(u, v)
                    moved.add_edge(v, u)
                assert all(moved.out_degree(v) == r + (v == new_root) for v in G)
                assert len(nx.descendants(moved, new_root)) == n - 1
                stats["surplus_moves"] += 1
            if r >= 2:
                for choice in (0, -1):
                    P_edges = [(v, sorted(D.successors(v))[choice]) for v in G]
                    P = nx.Graph()
                    P.add_nodes_from(G)
                    P.add_edges_from(P_edges)
                    assert P.number_of_edges() == n and is_spanning_map(P)
                    H = D.copy()
                    H.remove_edges_from(P_edges)
                    core = {root} | nx.descendants(H, root)
                    assert is_circuit(H.subgraph(core).to_undirected(), r - 1)
                    H_vertices, H_counts = edge_counts(H.to_undirected())
                    for mask, e in enumerate(H_counts):
                        if e > (r - 1) * mask.bit_count():
                            S = {H_vertices[i] for i in range(n) if mask >> i & 1}
                            assert core <= S
                    stats["rank_drop_core_checks"] += 1

        if r == 2:
            edges = list(G.edges())
            for size in range(2 * r):
                for F in combinations(edges, size):
                    complement = G.copy()
                    complement.remove_edges_from(F)
                    no_isolates = not list(nx.isolates(complement))
                    result = decompose_avoiding(G, r, F)
                    assert (result is not None) == no_isolates
                    for C in nx.connected_components(complement):
                        if nx.is_tree(complement.subgraph(C)):
                            assert len(C) == 1
                    stats["small_forbidden_sets"] += 1
                    if result is None:
                        stats["small_forbidden_saturated_failures"] += 1

    # Reproducible samples at higher rank, plus forced saturated failures.
    rng = random.Random(548)
    for r in range(3, 7):
        n = 2 * r + 2
        for trial in range(5):
            G = nx.complete_graph(n)
            G.remove_edges_from(rng.sample(list(G.edges()), r))
            assert is_circuit(G, r)
            edges = list(G.edges())
            for _ in range(100):
                F = rng.sample(edges, rng.randrange(2 * r))
                H = G.copy()
                H.remove_edges_from(F)
                no_isolates = not list(nx.isolates(H))
                assert (decompose_avoiding(G, r, F) is not None) == no_isolates
                stats["higher_r_forbidden_sets"] += 1
                if not no_isolates:
                    stats["higher_r_saturated_failures"] += 1
        G = nx.complete_graph(n)
        G.remove_edges_from((0, j) for j in range(1, r + 1))
        F = list(G.edges(0))
        assert len(F) == r + 1 <= 2 * r - 1
        assert decompose_avoiding(G, r, F) is None
        stats["higher_r_forbidden_sets"] += 1
        stats["higher_r_saturated_failures"] += 1

    # Sharpness of the 2r-1 threshold, even for a tree of maximum degree r.
    for r in range(2, 7):
        G, F = sharp_forbidden_example(r)
        assert is_circuit(G, r)
        R = nx.Graph()
        R.add_edges_from(F)
        assert nx.is_tree(R) and len(F) == 2 * r
        assert max(dict(R.degree()).values()) <= r
        complement = G.copy()
        complement.remove_edges_from(F)
        assert not list(nx.isolates(complement))
        assert sorted(len(C) for C in nx.connected_components(complement)) == [2, 2 * r + 1]
        assert decompose_avoiding(G, r, F) is None
        stats["sharpness_examples"] += 1

    # Complete bipartite r-circuits: exhaustive part-size inequalities.
    for r in range(1, 31):
        a, b = r + 1, r * (r + 1) + 1
        n, m = a + b, a * b
        assert m == r * n + 1
        for x in range(a + 1):
            for y in range(b + 1):
                if (x, y) != (a, b):
                    assert x * y <= r * (x + y)
                    stats["bipartite_subset_size_checks"] += 1
        assert n - 1 == (r + 1) * a
        if r >= 2:
            # A spanning (r-1)-circuit needs degree >= r at all b vertices.
            assert (r - 1) * n + 1 < r * b
        stats["bipartite_family_parameters"] += 1

    # A spanning map not compatible with the full decomposition can fail.
    H = nx.complete_graph(4)
    H.add_edge(4, 5)
    P = nx.Graph()
    P.add_nodes_from(range(6))
    P.add_edges_from([(0, 4), (0, 5), (1, 4), (1, 5), (2, 4), (3, 5)])
    G = nx.compose(H, P)
    assert is_circuit(G, 2) and is_spanning_map(P)
    assert set(nx.complete_graph(6).edges()) - set(G.edges()) == {(2, 5), (3, 4)}
    for edge in nx.complete_graph(4).edges():
        C = nx.complete_graph(4)
        C.remove_edge(*edge)
        assert is_circuit(C, 1)
        stats["incompatible_deletion_circuits"] += 1

    # A blocked-star decomposition exists for every r >= 2.
    for r in range(2, 7):
        G, P, H, high, eligible = blocked_star_decomposition(r)
        assert is_circuit(G, r) and is_circuit(H, r - 1) and is_spanning_map(P)
        assert set(v for v in G if G.degree(v) >= 2 * r + 1) == set(high)
        assert set(v for v in H if H.degree(v) >= 2 * r - 1) == set(eligible)
        assert all(G.degree(v) == 2 * r for v in eligible)
        assert all(H.degree(v) == 2 * r - 2 for v in high)
        # A shape-aware swap repairs this particular family.
        u = high[0]
        c = eligible[0]
        P2, H2 = P.copy(), H.copy()
        P2.remove_edge(u, 0)
        P2.add_edge(c, 0)
        H2.remove_edge(c, 0)
        H2.add_edge(u, 0)
        assert is_spanning_map(P2) and is_circuit(H2, r - 1)
        assert H2.degree(u) == 2 * r - 1
        stats["blocked_star_family_parameters"] += 1

    # The six-vertex instance: exhaustive non-induced embedding checks.
    G = nx.complete_graph(6)
    G.remove_edges_from([(0, 1), (2, 3)])
    H = nx.Graph()
    H.add_nodes_from(G)
    H.add_edges_from([(0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 5), (4, 5)])
    P = nx.Graph()
    P.add_nodes_from(G)
    P.add_edges_from(set(G.edges()) - set(H.edges()))
    assert is_circuit(G, 2) and is_circuit(H, 1) and is_spanning_map(P)
    _, counts = edge_counts(G)
    assert all(counts[s] < 2 * s.bit_count() for s in range(1, (1 << 6) - 1))
    R, T = nx.star_graph(3), nx.star_graph(5)
    smaller_embeddings = list(nx.algorithms.isomorphism.GraphMatcher(H, R).subgraph_monomorphisms_iter())
    assert len(smaller_embeddings) == 12
    for host_to_tree in smaller_embeddings:
        tree_to_host = {t: h for h, t in host_to_tree.items()}
        center = tree_to_host[0]
        assert center in (0, 1)
        assert G.degree(center) == 4
        assert len(set(G.neighbors(center)) - set(host_to_tree)) == 1
    full_embeddings = list(nx.algorithms.isomorphism.GraphMatcher(G, T).subgraph_monomorphisms_iter())
    assert len(full_embeddings) == 240
    stats["blocked_smaller_star_embeddings"] = len(smaller_embeddings)
    stats["full_star_embeddings_in_original"] = len(full_embeddings)
    # One genuine exchange repairs this example: no claim that all exchanges fail.
    H2, P2 = H.copy(), P.copy()
    H2.remove_edge(0, 2)
    H2.add_edge(2, 4)
    P2.remove_edge(2, 4)
    P2.add_edge(0, 2)
    assert is_circuit(H2, 1) and is_spanning_map(P2)
    assert H2.degree(4) == 3 and G.degree(4) == 5

    # Circuits may have bridges, ruling out strong connectivity in general.
    for r in range(1, 4):
        a = 2 * r + 1
        G = nx.disjoint_union(nx.complete_graph(a), nx.complete_graph(a))
        G.add_edge(0, a)
        assert is_circuit(G, r)
        assert list(nx.bridges(G)) == [(0, a)]
        stats["bridge_circuits"] += 1

    # Even-k parity obstruction: doubling need not itself give a circuit.
    G = nx.complete_bipartite_graph(3, 3)
    G.add_edge(0, 1)
    vertices, counts = edge_counts(G)
    assert len(G) == 6 and G.number_of_edges() == 10
    assert all(2 * counts[s] <= 3 * s.bit_count() for s in range((1 << 6) - 1))
    D = nx.MultiGraph()
    D.add_nodes_from(G)
    for edge in G.edges():
        D.add_edge(*edge)
        D.add_edge(*edge)
    assert D.number_of_edges() == 20 and not is_circuit(D, 3)
    for u, v, key in list(D.edges(keys=True)):
        C = D.copy()
        C.remove_edge(u, v, key)
        assert is_circuit(C, 3)
        assert set(C.edges()) == set(G.edges())
        stats["even_single_copy_deletions"] += 1

    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_HASH
    print(json.dumps(dict(sorted(stats.items())), indent=2))
    print("All circuit checks passed; Spec.lean is unchanged.")


if __name__ == "__main__":
    run_checks()
