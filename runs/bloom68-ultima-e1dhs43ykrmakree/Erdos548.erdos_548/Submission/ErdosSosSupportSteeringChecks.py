#!/usr/bin/env python3
"""Exact checks for the support-steering obstruction (not an Erdos--Sos proof).

The family and its obstruction are proved in ErdosSosSupportSteering.md.
Only the standard library and NetworkX are needed. No random sampling is used.
Run with --atlas to check every <=3-edge path in every atlas 2-circuit.
"""
from collections import Counter, deque
from itertools import combinations
from pathlib import Path
import argparse
import hashlib
import json

import networkx as nx
from ErdosSosCircuitChecks import SPEC_HASH, edge_counts, is_circuit, is_spanning_map


def edge_set(G):
    return {frozenset(e) for e in G.edges()}


def obstruction(r, full_tree=True):
    """Two adjacent degree-(r+1) vertices added to a tight K_(2r+1).

    full_tree=True gives the adjacent double r-star, with 2r-1 edges.
    False gives its r+1-edge subtree, also already an obstruction.
    """
    assert r >= 2
    N = 2 * r + 1
    u, v = N, N + 1
    W = set(range(N))
    G = nx.complete_graph(N)
    G.add_edges_from((u, a) for a in range(r))
    G.add_edges_from((v, a) for a in range(r))
    G.add_edge(u, v)
    F = nx.Graph()
    F.add_edges_from((u, a) for a in range(r))
    F.add_edge(v, 0)
    if full_tree:
        F.add_edges_from((0, b) for b in range(r, 2 * r - 2))

    # Cyclic-distance factors partition K_N into r spanning 2-factors.
    factors = []
    for i in range(1, r + 1):
        R = nx.Graph()
        R.add_nodes_from(G)
        R.add_edges_from((j, (j + i) % N) for j in range(N))
        factors.append(R)
    P = factors[0]
    P.add_edges_from([(u, v), (v, 1)])
    for i in range(2, r + 1):
        b = 0 if i == 2 else i - 1
        factors[i - 1].add_edges_from([(u, i - 2), (v, b)])
    extra = (u, r - 1)

    # An explicit quota orientation of the remainder, root u.
    D = nx.DiGraph()
    D.add_nodes_from(G)
    for i in range(2, r + 1):
        D.add_edges_from((j, (j + i) % N) for j in range(N))
        b = 0 if i == 2 else i - 1
        D.add_edges_from([(u, i - 2), (v, b)])
    D.add_edge(*extra)
    return G, F, factors, extra, D, W, u, v


def component_data(n, edges, mask):
    parent = list(range(n))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    todo = mask
    while todo:
        bit = todo & -todo
        todo ^= bit
        a, b = edges[bit.bit_length() - 1]
        a, b = find(a), find(b)
        if a != b:
            parent[a] = b
    roots = [find(a) for a in range(n)]
    nv = Counter(roots)
    ne = Counter()
    todo = mask
    while todo:
        bit = todo & -todo
        todo ^= bit
        a, _ = edges[bit.bit_length() - 1]
        ne[roots[a]] += 1
    return roots, nv, ne


def map_mask(n, edges, mask):
    if mask.bit_count() != n:
        return False
    _, nv, ne = component_data(n, edges, mask)
    return all(ne[c] == size for c, size in nv.items())


def compatible_bicircular_core(n, edges, mask):
    """For n+1 edges, return the unique circuit mask, or None if incompatible.

    Map+extra is possible iff no component is a tree: then exactly one
    component is bicyclic and all others are unicyclic. Its leaf-pruned
    core is the unique bicircular circuit (including a handcuff bridge).
    """
    assert mask.bit_count() == n + 1
    roots, nv, ne = component_data(n, edges, mask)
    if any(ne[c] < size for c, size in nv.items()):
        return None
    excess = [c for c, size in nv.items() if ne[c] == size + 1]
    assert len(excess) == 1
    c = excess[0]
    adjacency = [0] * n
    core = 0
    todo = mask
    while todo:
        bit = todo & -todo
        todo ^= bit
        a, b = edges[bit.bit_length() - 1]
        if roots[a] == c:
            core |= bit
            adjacency[a] |= bit
            adjacency[b] |= bit
    queue = deque(a for a in range(n) if roots[a] == c and adjacency[a].bit_count() < 2)
    while queue:
        a = queue.popleft()
        if adjacency[a].bit_count() != 1:
            continue
        bit = adjacency[a]
        x, y = edges[bit.bit_length() - 1]
        b = y if x == a else x
        adjacency[a] = 0
        adjacency[b] ^= bit
        core ^= bit
        if adjacency[b].bit_count() < 2:
            queue.append(b)
    return core


def graph_from_mask(n, edges, mask, retain_isolates=True):
    H = nx.Graph()
    if retain_isolates:
        H.add_nodes_from(range(n))
    H.add_edges_from(e for i, e in enumerate(edges) if mask >> i & 1)
    return H


def check_family(stats):
    for r in range(2, 31):
        for full_tree in (False, True):
            G, F, maps, extra, D, W, u, v = obstruction(r, full_tree)
            n, q = len(G), r - 1
            assert G.number_of_edges() == r * n + 1
            assert nx.is_tree(F)
            assert F.number_of_edges() == (2 * r - 1 if full_tree else r + 1)
            assert F.number_of_edges() <= 2 * r - 1
            assert max(dict(F.degree()).values()) == r
            if full_tree:
                assert F.degree(u) == F.degree(0) == r
                assert all(F.degree(a) == 1 for a in F if a not in (u, 0))
            assert edge_set(F) <= edge_set(G)
            assert G.degree(u) == G.degree(v) == r + 1
            G_minus_F = G.copy()
            G_minus_F.remove_edges_from(F.edges())
            assert not list(nx.isolates(G_minus_F))
            assert all(is_spanning_map(M) and M.number_of_edges() == n for M in maps)
            partition = [e for M in maps for e in edge_set(M)] + [frozenset(extra)]
            assert len(partition) == len(set(partition)) == G.number_of_edges()
            assert set(partition) == edge_set(G)
            assert not edge_set(F) & edge_set(maps[0])
            assert u in extra and F.degree(u) == max(dict(F.degree()).values())
            H = G.copy()
            H.remove_edges_from(maps[0].edges())
            assert edge_set(D) == edge_set(H)
            assert D.number_of_edges() == H.number_of_edges()
            assert all(D.out_degree(a) == q + (a == u) for a in G)
            assert set(nx.descendants(D, u)) | {u} == W | {u}
            assert H.degree(v) == r - 1
            S = W | {u}
            assert G.subgraph(S).number_of_edges() == r * len(S)
            assert G_minus_F.subgraph(S).degree(u) == 0
            assert H.subgraph(S).number_of_edges() == q * len(S) + 1
            stats['explicit_family_decompositions'] += 1
            if r <= 6:
                assert is_circuit(G, r)
                assert is_circuit(H.subgraph(S).copy(), q)
                vertices, counts = edge_counts(G)
                tight = {
                    frozenset(vertices[i] for i in range(n) if mask >> i & 1)
                    for mask in range(1, (1 << n) - 1)
                    if counts[mask] == r * mask.bit_count()
                }
                assert tight == {frozenset(W), frozenset(W | {u}), frozenset(W | {v})}
                stats['exhaustive_family_circuit_checks'] += 1


def check_pilot_all_red_maps(stats):
    G, F, _, _, _, W, u, v = obstruction(2)
    n = len(G)
    candidates = sorted(tuple(sorted(e)) for e in edge_set(G) - edge_set(F))
    all_edges = sorted(tuple(sorted(e)) for e in edge_set(G))
    index = {e: i for i, e in enumerate(all_edges)}
    full = (1 << len(all_edges)) - 1
    for chosen in combinations(candidates, n):
        stats['pilot_red_edge_subsets'] += 1
        P = nx.Graph()
        P.add_nodes_from(G)
        P.add_edges_from(chosen)
        if not is_spanning_map(P):
            continue
        stats['pilot_avoiding_spanning_maps'] += 1
        assert P.degree(u) == 1 and P.has_edge(u, v)
        assert P.degree(v) >= 2
        H = G.copy()
        H.remove_edges_from(P.edges())
        assert H.degree(v) <= 1
        pmask = sum(1 << index[e] for e in chosen)
        cmask = compatible_bicircular_core(n, all_edges, full ^ pmask)
        # Independent compatibility test: try every possible extra edge.
        valid_extras = []
        for edge in list(H.edges()):
            Q = H.copy()
            Q.remove_edge(*edge)
            if is_spanning_map(Q):
                valid_extras.append(frozenset(edge))
        assert (cmask is not None) == bool(valid_extras)
        if cmask is None:
            continue
        stats['pilot_compatible_avoiding_maps'] += 1
        C = graph_from_mask(n, all_edges, cmask, retain_isolates=False)
        assert is_circuit(C, 1)
        assert edge_set(C) == set(valid_extras)
        assert v not in C
        assert not edge_set(F) <= edge_set(C)


def path_masks(G, max_length=3):
    edges = sorted(tuple(sorted(e)) for e in G.edges())
    index = {e: i for i, e in enumerate(edges)}
    paths = [set() for _ in range(max_length + 1)]

    def extend(seq, mask):
        if len(seq) > 1:
            paths[len(seq) - 1].add(mask)
        if len(seq) == max_length + 1:
            return
        for w in G.neighbors(seq[-1]):
            if w not in seq:
                e = tuple(sorted((seq[-1], w)))
                extend(seq + (w,), mask | (1 << index[e]))

    for v in G:
        extend((v,), 0)
    return edges, paths


def check_atlas_paths(stats):
    for atlas_index, original in enumerate(nx.graph_atlas_g()):
        if not is_circuit(original, 2):
            continue
        G = nx.convert_node_labels_to_integers(original)
        n = len(G)
        edges, paths = path_masks(G)
        full = (1 << len(edges)) - 1
        cores = set()
        for chosen in combinations(range(len(edges)), n):
            pmask = sum(1 << i for i in chosen)
            if map_mask(n, edges, pmask):
                core = compatible_bicircular_core(n, edges, full ^ pmask)
                if core is not None:
                    cores.add(core)
        assert cores
        stats['atlas_2_circuit_hosts'] += 1
        host_failure = False
        vertices, counts = edge_counts(G)
        tight_sets = [
            {vertices[i] for i in range(n) if mask >> i & 1}
            for mask in range(1, (1 << n) - 1)
            if counts[mask] == 2 * mask.bit_count()
        ]
        for length in range(1, 4):
            for F in paths[length]:
                stats[f'atlas_paths_{length}_edges'] += 1
                if not any(F & C == F for C in cores):
                    stats[f'atlas_unsupported_paths_{length}_edges'] += 1
                    host_failure = True
                    # The short pilot is minimal in order and path length
                    # within this exact atlas search, not an unrestricted claim.
                    assert n == 7 and length == 3, (atlas_index, n, length, F)
                    protected = {e for i, e in enumerate(edges) if F >> i & 1}
                    T = {a for e in protected for a in e}
                    remaining = G.copy()
                    remaining.remove_edges_from(protected)
                    certificates = [
                        S for S in tight_sets
                        if not T <= S and list(nx.isolates(remaining.subgraph(S)))
                    ]
                    assert certificates
                    stats['atlas_failed_paths_with_tight_isolate_certificate'] += 1
        if host_failure:
            low = {a for a in G if G.degree(a) == 3}
            assert len(low) == 2 and G.subgraph(low).number_of_edges() == 1
            W = set(G) - low
            assert G.subgraph(W).number_of_edges() == 10
            stats['atlas_hosts_with_unsupported_paths'] += 1


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--atlas', action='store_true')
    args = parser.parse_args()
    spec = Path(__file__).with_name('Spec.lean')
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_HASH
    stats = Counter()
    check_family(stats)
    check_pilot_all_red_maps(stats)
    if args.atlas:
        check_atlas_paths(stats)
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_HASH
    print(json.dumps(dict(sorted(stats.items())), indent=2))
    print('Support-steering obstruction checks passed; Spec.lean is unchanged.')


if __name__ == '__main__':
    main()
