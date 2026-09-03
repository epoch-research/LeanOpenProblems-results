#!/usr/bin/env python3
"""Exact certificates for ForestInterfaceFindings.md.

Containment is NON-INDUCED. These checks do not prove unrestricted W_k or
Erdos--Sos, and do not write Spec.lean. Requires NetworkX.
"""
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations, product
from pathlib import Path
import hashlib
import random

import networkx as nx

SPEC_HASH = "674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103"


def verify_injection(F, H, phi):
    assert set(phi) == set(F)
    assert len(set(phi.values())) == len(F)
    assert set(phi.values()) <= set(H)
    assert all(H.has_edge(phi[u], phi[v]) for u, v in F.edges())


def order_scores(G, order):
    assert len(order) == len(G) and set(order) == set(G)
    earlier = set()
    scores = []
    for v in order:
        scores.append(G.degree(v) + len(set(G[v]) & earlier))
        earlier.add(v)
    return scores


def wk_order(G, k):
    remaining, active, order = set(G), set(), []
    while remaining:
        v = next((v for v in remaining
                  if G.degree(v) + len(set(G[v]) & active) >= k), None)
        if v is None:
            return None
        remaining.remove(v)
        active.add(v)
        order.append(v)
    return order


def incident_edges(G, X):
    return sum(u in X or v in X for u, v in G.edges())


def root_matching(H, images):
    """Find the Hall matching from a set of roots to vertices outside that set."""
    R = set(images)
    assert len(R) == len(images)
    K = nx.Graph()
    left = [("left", i) for i in range(len(images))]
    K.add_nodes_from(left)
    for i, r in enumerate(images):
        K.add_edges_from((left[i], ("right", v)) for v in H[r] if v not in R)
    matching = nx.algorithms.bipartite.maximum_matching(K, top_nodes=left)
    assert all(v in matching for v in left)
    return [matching[v][1] for v in left]


def extend_nontrivial_cores(F, H, phi):
    """Extend connected, nontrivial partial cores in every forest component."""
    e = F.number_of_edges()
    assert min(dict(H.degree()).values()) >= e
    assert not any(nx.triangles(H).values())
    phi = dict(phi)
    for C in nx.connected_components(F):
        P = F.subgraph(C & set(phi))
        assert len(P) >= 2 and nx.is_connected(P)
    used = set(phi.values())
    while len(phi) < len(F):
        u, v = next((u, v) for u in phi for v in F[u] if v not in phi)
        P = F.subgraph(phi)
        occupied_neighbors = set(H[phi[u]]) & used
        preimage = {x for x, y in phi.items() if y in occupied_neighbors}
        assert not F.subgraph(preimage).number_of_edges()
        assert len(occupied_neighbors) <= P.number_of_edges() < e
        w = next(w for w in H[phi[u]] if w not in used)
        phi[v] = w
        used.add(w)
    verify_injection(F, H, phi)
    return phi


def rooted_triangle_free_forest(F, H, root_map):
    """The proved one-root-per-nontrivial-component construction."""
    assert len(F) and nx.is_forest(F)
    assert min(dict(F.degree()).values()) >= 1
    assert not any(nx.triangles(H).values())
    assert min(dict(H.degree()).values()) >= F.number_of_edges()
    components = list(nx.connected_components(F))
    assert all(len(C & set(root_map)) == 1 for C in components)
    assert len(root_map) == len(components)
    roots = list(root_map)
    images = [root_map[r] for r in roots]
    new_images = root_matching(H, images)
    phi = dict(root_map)
    for r, y in zip(roots, new_images):
        child = next(iter(F[r]))
        assert child not in phi
        phi[child] = y
    phi = extend_nontrivial_cores(F, H, phi)
    assert all(phi[r] == x for r, x in root_map.items())
    return phi


def rooted_tree_via_deletion(T, G, u, s):
    """Triangle-free corollary: d(s)>=k and delta(G-s)>=k-d_T(u)."""
    k = T.number_of_edges()
    assert G.degree(s) >= k and not any(nx.triangles(G).values())
    H = G.subgraph(set(G) - {s}).copy()
    F = T.subgraph(set(T) - {u}).copy()
    assert min(dict(H.degree()).values()) >= F.number_of_edges()
    nontrivial = [C for C in nx.connected_components(F) if len(C) >= 2]
    nontrivial_vertices = set().union(*nontrivial) if nontrivial else set()
    F1 = F.subgraph(nontrivial_vertices).copy()
    roots = []
    for C in nontrivial:
        attached = set(T[u]) & C
        assert len(attached) == 1
        roots.append(next(iter(attached)))
    images = list(G[s])[:len(roots)]
    phi = rooted_triangle_free_forest(F1, H, dict(zip(roots, images))) if roots else {}
    phi[u] = s
    unused_neighbors = iter(set(G[s]) - set(phi.values()))
    for x in set(T) - set(phi):
        assert T.degree(x) == 1 and T.has_edge(x, u)
        phi[x] = next(unused_neighbors)
    verify_injection(T, G, phi)
    assert phi[u] == s
    return phi


@lru_cache(None)
def trees(n):
    return tuple(nx.nonisomorphic_trees(n)) if n >= 2 else (nx.empty_graph(1),)


def check_triangle_free_forests(atlas):
    forests = [F for F in atlas if len(F) >= 2 and nx.is_forest(F)
               and min(dict(F.degree()).values()) >= 1]
    hosts = [H for H in atlas if len(H) and not any(nx.triangles(H).values())]
    checks, hall_checks, nx_checks = 0, 0, 0
    for H in hosts:
        delta = min(dict(H.degree()).values())
        for p in range(1, delta + 1):
            for R in combinations(H, p):
                Rset = set(R)
                for q in range(1, p + 1):
                    for X in combinations(R, q):
                        Y = set().union(*(set(H[v]) for v in X)) - Rset
                        assert len(Y) >= len(X)
                        hall_checks += 1
        for F in forests:
            if len(F) > len(H) or F.number_of_edges() > delta:
                continue
            components = [sorted(C) for C in nx.connected_components(F)]
            for roots in product(*components):
                for images in permutations(H, len(roots)):
                    phi = rooted_triangle_free_forest(F, H, dict(zip(roots, images)))
                    checks += 1
                    # Independent non-induced matcher with prescribed roots.
                    if checks % 97 == 0:
                        HH, FF = H.copy(), F.copy()
                        for x in HH:
                            HH.nodes[x]["root"] = -1
                        for x in FF:
                            FF.nodes[x]["root"] = -1
                        for i, (r, image) in enumerate(zip(roots, images)):
                            HH.nodes[image]["root"] = i
                            FF.nodes[r]["root"] = i
                        match = nx.algorithms.isomorphism.GraphMatcher(
                            HH, FF, node_match=lambda a, b: a["root"] == b["root"])
                        assert match.subgraph_is_monomorphic()
                        nx_checks += 1
                    assert all(phi[r] == x for r, x in zip(roots, images))
    print(f"Triangle-free forest theorem: {checks} atlas prescribed-root constructions; "
          f"{hall_checks} root-matching Hall inequalities; {nx_checks} independent matcher checks.")


def check_random_triangle_free_forests(count=2000):
    rng = random.Random(844031)
    for case in range(count):
        if case % 2:
            # Nonbipartite triangle-free examples: independent blow-ups of C5.
            width = rng.randint(1, 8)
            parts = [list(range(i * width, (i + 1) * width)) for i in range(5)]
            H = nx.Graph()
            for i in range(5):
                H.add_edges_from(product(parts[i], parts[(i + 1) % 5]))
        else:
            H = nx.complete_bipartite_graph(rng.randint(2, 14), rng.randint(2, 18))
        delta = min(dict(H.degree()).values())
        e = rng.randint(1, delta)
        p = rng.randint(1, e)
        sizes = [1] * p
        for _ in range(e - p):
            sizes[rng.randrange(p)] += 1
        F = nx.Graph()
        roots = []
        for size in sizes:
            T = nx.from_prufer_sequence([rng.randrange(size + 1) for _ in range(size - 1)])
            roots.append(len(F) + rng.randrange(size + 1))
            F = nx.disjoint_union(F, T)
        images = rng.sample(list(H), p)
        rooted_triangle_free_forest(F, H, dict(zip(roots, images)))
    print(f"Triangle-free forest construction: {count} additional deterministic random checks.")


def check_wk_high_degree_corollary(atlas):
    checks = 0
    for G in atlas:
        if len(G) < 2 or any(nx.triangles(G).values()):
            continue
        for k in range(1, len(G)):
            if wk_order(G, k) is None:
                continue
            assert min(dict(G.degree()).values()) >= (k + 1) // 2
            seeds = [s for s in G if G.degree(s) >= k]
            for T in trees(k + 1):
                for u in T:
                    if T.degree(u) < k // 2 + 1:
                        continue
                    for s in seeds:
                        rooted_tree_via_deletion(T, G, u, s)
                        checks += 1
    print(f"Triangle-free W_k high-tree-degree corollary: {checks} atlas rooted constructions.")


def two_wing_host(k):
    assert k % 2 == 0
    G = nx.Graph()
    s = ("s",)
    A = [[("A", i, j) for j in range(k // 2)] for i in range(2)]
    B = [[("B", i, j) for j in range(k - 2)] for i in range(2)]
    for i in range(2):
        G.add_edges_from(product(A[i], B[i] + [s]))
    order = [s] + A[0] + A[1] + B[0] + B[1]
    assert order_scores(G, order) == [k] * len(G)
    return G, s, A, B


def check_whole_smaller_class_obstruction():
    G, s, A, B = two_wing_host(12)
    T = nx.Graph()
    z = ("z",)
    hubs = [("h", i) for i in range(3)]
    for i, h in enumerate(hubs):
        T.add_edge(z, h)
        T.add_edges_from((h, ("leaf", i, j)) for j in range(3))
    small, large = set(hubs), set(T) - set(hubs)
    assert (len(G), G.number_of_edges()) == (33, 132)
    assert [v for v in G if G.degree(v) >= 12] == [s]
    assert (len(small), len(large), T.number_of_edges()) == (3, 10, 12)
    assert {v for v in T if T.degree(v) == max(dict(T.degree()).values())} == small
    for h in small:
        F = T.subgraph(set(T) - {h})
        big = next(C for C in nx.connected_components(F) if len(C) > 1)
        assert z in big and (len(big & small), len(big & large)) == (2, 7)
        assert len(big & large) > len(A[0]) == len(A[1])
        assert F.number_of_edges() == 8 > min(dict(G.subgraph(set(G) - {s}).degree()).values()) == 6
    phi = dict(zip(hubs, A[0]))
    phi.update(zip(sorted(large), B[0]))
    verify_injection(T, G, phi)
    phi = {z: s, **dict(zip(hubs, A[0]))}
    phi.update(zip(sorted(large - {z}), B[0]))
    verify_injection(T, G, phi)
    print("W_12 smaller-class obstruction: all three smaller-class vertices excluded at the unique seed "
          "by 7>6; both an unrooted copy and a larger-class root at the seed verified.")


def incidence_interface_host(q=16):
    """Triangle-free ID_13 example; q>=16 makes S exactly the maximum-degree set."""
    assert q >= 11
    A = [("A", i) for i in range(3)]
    C = [("C", i) for i in range(31)]
    B = [("B", i) for i in range(7)]
    S = [("S", i) for i in range(3)]
    G, weights, wings = nx.Graph(), {}, {}

    def edge(u, v, at_u):
        assert not G.has_edge(u, v)
        G.add_edge(u, v)
        weights[u, v], weights[v, u] = Fraction(at_u), 1 - Fraction(at_u)

    for a, b in product(A, B):
        edge(a, b, Fraction(124, 287))
    for c, b in product(C, B):
        edge(c, b, Fraction(247, 287))
    for s, a in product(S, A):
        edge(a, s, 1)
    for i, j in combinations(range(3), 2):
        P = [("P", i, j, v) for v in range(q)]
        Q = [("Q", i, j, v) for v in range(q)]
        wings[i, j] = (P, Q)
        for p, r in product(P, Q):
            edge(p, r, Fraction(1, 2))
        for p in P:
            edge(S[i], p, Fraction(1, 3))
        for r in Q:
            edge(S[j], r, Fraction(1, 3))
    H = G.subgraph(set(G) - set(S)).copy()
    return G, H, S, A, B, C, wings, weights


def check_incidence_interface_obstruction():
    q, k, r = 16, 13, 3
    G, H, S, A, B, C, wings, weights = incidence_interface_host(q)
    assert (len(G), G.number_of_edges()) == (140, 1111)
    assert len(H) == 137 and min(dict(H.degree()).values()) == k - 2 * r == 7
    assert nx.is_connected(G) and not any(nx.triangles(G).values())
    assert not G.subgraph(S).number_of_edges()
    assert set(S) == {v for v in G if G.degree(v) == max(dict(G.degree()).values())}
    assert all(G.degree(s) == 35 >= k for s in S)
    order = S + A + B + C + sum((P + Q for P, Q in wings.values()), [])
    scores = order_scores(G, order)
    assert min(scores) >= k
    horder = order[len(S):]
    hscores = order_scores(H, horder)
    for v, gs, hs in zip(horder, scores[len(S):], hscores):
        deleted_neighbors = len(set(G[v]) & set(S))
        assert hs == gs - 2 * deleted_neighbors
        assert hs >= k - 2 * deleted_neighbors

    # A COMPLETE incidence certificate, not a sample: each edge's two weights
    # sum to one, and every vertex receives load strictly greater than six.
    for u, v in G.edges():
        assert weights[u, v] >= 0 and weights[v, u] >= 0
        assert weights[u, v] + weights[v, u] == 1
    load = {v: sum((weights[v, w] for w in G[v]), Fraction(0)) for v in G}
    assert all(load[v] == Fraction(247, 41) for v in A + B + C)
    assert all(load[s] == Fraction(32, 3) for s in S)
    assert all(load[v] == Fraction(26, 3) for P, Q in wings.values() for v in P + Q)
    assert min(load.values()) > Fraction(k - 1, 2)
    assert sum(load.values()) == G.number_of_edges()
    rng = random.Random(88301)
    for _ in range(200):
        X = {v for v in G if rng.randrange(2)}
        assert X
        assert incident_edges(G, X) >= sum(load[v] for v in X) > 6 * len(X)

    T = nx.path_graph(11)
    T.add_edges_from([(1, 11), (5, 12), (9, 13)])
    U = {1, 5, 9}
    smaller = {1, 3, 5, 7, 9}
    assert nx.is_tree(T) and T.number_of_edges() == k
    assert len(smaller) == 5 < len(T) - len(smaller) == 9
    assert not T.subgraph(smaller).number_of_edges()
    assert U == {v for v in T if T.degree(v) == 3}
    assert all(T.degree(v) <= 2 for v in set(T) - U)
    assert sum(T.degree(u) for u in U) == 9 >= 2 * r
    F = T.subgraph(set(T) - U).copy()
    assert (len(F), F.number_of_edges()) == (11, 4)
    paths = [(2, 3, 4), (6, 7, 8)]
    isolates = {0, 10, 11, 12, 13}
    assert {frozenset(D) for D in nx.connected_components(F)} == {
        frozenset(paths[0]), frozenset(paths[1]), *(frozenset([x]) for x in isolates)}
    core = set(A + B + C)
    component_copies = {}
    for si, sj in permutations(S, 2):
        copies = []
        for middle in H:
            left = set(H[middle]) & set(G[si])
            right = set(H[middle]) & set(G[sj])
            copies.extend((x, middle, y) for x, y in product(left, right) if x != y)
        # This enumerates EVERY ordered, list-respecting P3 in H.
        assert len(copies) == 42
        assert all(x in A and y in A and middle in B for x, middle, y in copies)
        component_copies[si, sj] = copies
    hall_count = 0
    for images in permutations(S):
        assignment = dict(zip(sorted(U), images))
        lists = {}
        for x in F:
            attached = set(T[x]) & U
            lists[x] = set(H)
            for u in attached:
                lists[x] &= set(G[assignment[u]])
            assert len(lists[x]) >= len(F)
        # Verify Hall for ALL subsets of all forest vertices.
        vertices = list(F)
        for mask in range(1, 1 << len(vertices)):
            subset = [vertices[i] for i in range(len(vertices)) if mask >> i & 1]
            assert len(set().union(*(lists[v] for v in subset))) >= len(subset)
            hall_count += 1
        for x, middle, y in paths:
            assert lists[x] & core == lists[y] & core == set(A)
            # Exhaust all connected host components outside the core. If both
            # endpoint lists meet a wing, they lie in OPPOSITE bipartition sides.
            for P, Q in wings.values():
                V = set(P + Q)
                Lx, Ly = lists[x] & V, lists[y] & V
                if Lx and Ly:
                    assert (Lx == set(P) and Ly == set(Q)) or (Lx == set(Q) and Ly == set(P))
            local = {x: A[0], middle: B[0], y: A[1]}
            verify_injection(F.subgraph([x, middle, y]), H, local)
            assert all(local[v] in lists[v] for v in local)
        for x in isolates:
            assert lists[x]
        # Each path must therefore consume TWO distinct A vertices. The two
        # paths are disjoint, making a simultaneous embedding impossible.
        assert 2 * len(paths) == 4 > len(A) == 3
        first = component_copies[assignment[1], assignment[5]]
        second = component_copies[assignment[5], assignment[9]]
        assert all(set(P) & set(Q) for P, Q in product(first, second))

    # Unrooted embedding avoiding S altogether.
    P, Q = wings[0, 1]
    phi = dict(zip(sorted(smaller), P))
    phi.update(zip(sorted(set(T) - smaller), Q))
    verify_injection(T, G, phi)
    assert not set(phi.values()) & set(S)

    # Keeping the same S but changing one chosen TREE vertex repairs the issue.
    P02, Q02 = wings[0, 2]
    P01, _ = wings[0, 1]
    _, Q12 = wings[1, 2]
    phi = {0: A[0], 1: S[0], 2: A[1], 3: S[1], 4: A[2], 5: S[2],
           6: Q02[0], 7: P02[0], 8: Q02[1], 9: P02[1], 10: Q02[2],
           11: P01[0], 12: Q12[0], 13: Q02[3]}
    verify_injection(T, G, phi)
    Uprime = {1, 3, 5}
    assert {phi[u] for u in Uprime} == set(S)
    assert sum(T.degree(u) for u in Uprime) == 8 >= 2 * r
    assert T.subgraph(set(T) - Uprime).number_of_edges() == 5 <= 7
    print("Main obstruction: triangle-free ID_13 host n=140,m=1111; delta(H)=7=k-2r; "
          "S is the independent set of all three maximum-degree vertices (degree 35).")
    print(f"  Exact incidence loads: core=247/41, seeds=32/3, wings=26/3, all >6. "
          f"All six U-to-S bijections blocked despite {hall_count} verified Hall inequalities "
          "and individual component embeddings; changing U to {1,3,5} repairs the embedding.")
    print("  Complete component enumeration: exactly 42 marked P3 copies per ordered seed pair; "
          "every pair of component copies intersects.")

    G11, H11, S11, A11, B11, C11, wings11, weights11 = incidence_interface_host(11)
    assert (len(G11), G11.number_of_edges()) == (110, 676)
    assert min(dict(H11.degree()).values()) == 7
    assert not any(nx.triangles(G11).values())
    assert all(sum(weights11[v, w] for w in G11[v]) > 6 for v in G11)
    order11 = S11 + A11 + B11 + C11 + sum((P + Q for P, Q in wings11.values()), [])
    assert min(order_scores(G11, order11)) >= 13
    assert all(G11.degree(s) == 25 < 34 for s in S11)


def check_basic_obstructions():
    # Triangle-freeness cannot be dropped from the prescribed-root theorem.
    H = nx.disjoint_union(nx.complete_graph(3), nx.complete_graph(3))
    H.add_edge(2, 3)
    assert nx.is_connected(H) and min(dict(H.degree()).values()) == 2
    assert (set(H[0]) | set(H[1])) - {0, 1} == {2}
    # Two disjoint edges with roots at 0 and 1 cannot extend: both need vertex 2.

    # More than one mark in a component cannot be allowed merely by large lists.
    H = nx.complete_bipartite_graph(3, 3)
    F = nx.path_graph(3)
    assert min(dict(H.degree()).values()) >= F.number_of_edges()
    assert len({0, 1, 2}) == len({3, 4, 5}) == len(F)
    for middle in H:
        assert not (set(H[middle]) & {0, 1, 2} and set(H[middle]) & {3, 4, 5})

    # Requested compatibility with K_{2,7}: the bad fixed-root problem fails
    # the NEW sufficient condition delta(G-s)>=e(T-u), so there is no conflict.
    G = nx.complete_bipartite_graph(2, 7)
    T, u, s = nx.path_graph(5), 2, 0
    H = G.subgraph(set(G) - {s})
    F = T.subgraph(set(T) - {u})
    assert min(dict(H.degree()).values()) == 1 < F.number_of_edges() == 2
    GG, TT = G.copy(), T.copy()
    nx.set_node_attributes(GG, False, "root")
    nx.set_node_attributes(TT, False, "root")
    GG.nodes[s]["root"] = TT.nodes[u]["root"] = True
    assert not nx.algorithms.isomorphism.GraphMatcher(
        GG, TT, node_match=lambda a, b: a["root"] == b["root"]).subgraph_is_monomorphic()
    for mask in range(1, 1 << len(G)):
        X = {v for v in G if mask >> v & 1}
        assert 2 * incident_edges(G, X) > 3 * len(X)

    # Requested W_14 maximum-root example also lies outside the sufficient bound.
    G, s, A, B = two_wing_host(14)
    T = nx.Graph()
    for i in range(1, 4):
        T.add_edges_from([(("h", 0), ("c", i)), (("c", i), ("h", i))])
        T.add_edges_from((("h", i), ("leaf", i, j)) for j in range(3 if i < 3 else 2))
    H = G.subgraph(set(G) - {s})
    for u in [("h", 1), ("h", 2)]:
        assert min(dict(H.degree()).values()) == 7 < T.number_of_edges() - T.degree(u) == 10
    print("Boundary checks: connected two-triangle fixed-root obstruction, two-mark parity obstruction, "
          "K_{2,7} incidence/root obstruction, and compatibility with the stated W_14 example verified.")


def main():
    spec = Path(__file__).with_name("Spec.lean")
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_HASH
    atlas = nx.graph_atlas_g()
    check_triangle_free_forests(atlas)
    check_random_triangle_free_forests()
    check_wk_high_degree_corollary(atlas)
    check_basic_obstructions()
    check_whole_smaller_class_obstruction()
    check_incidence_interface_obstruction()
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_HASH
    print("All checks passed. Spec.lean is unchanged. Unrestricted W_k and Erdős–Sós remain unproved.")


if __name__ == "__main__":
    main()
