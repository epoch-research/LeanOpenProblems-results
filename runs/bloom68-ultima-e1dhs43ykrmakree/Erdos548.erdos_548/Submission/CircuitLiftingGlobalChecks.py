#!/usr/bin/env python3
"""Exact supplemental audits for CircuitLiftingGlobalFindings.md.

This checks proved identities/operations, not a proposed ES lifting theorem.
No search for new cut counterexamples is performed. NetworkX + standard library.
"""
from collections import Counter
from itertools import combinations, permutations
from math import comb, factorial
from pathlib import Path
import hashlib
import networkx as nx

STATS = Counter()
SPEC_HASH = "674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103"


def submasks(mask):
    x = mask
    while True:
        yield x
        if not x:
            break
        x = (x - 1) & mask


def counts(G):
    """Direct induced-edge counts, including distinct parallel edges."""
    vs = list(G)
    index = {v: i for i, v in enumerate(vs)}
    edge_masks = [(1 << index[u]) | (1 << index[v]) for u, v in G.edges()]
    return vs, [sum((s & e) == e for e in edge_masks)
                for s in range(1 << len(vs))]


def circuit(G, r):
    if not len(G) or G.number_of_edges() != r * len(G) + 1:
        return False
    _, ec = counts(G)
    return all(ec[s] <= r * s.bit_count() for s in range(len(ec) - 1))


def orientation(G, r, z):
    """Endpoint-slot Hall matching, independently constructed here."""
    es = sorted(tuple(sorted(e)) for e in G.edges())
    slots = [(v, j) for v in sorted(G) for j in range(r + (v == z))]
    at = {v: [i for i, (x, _) in enumerate(slots) if x == v] for v in G}
    allowed = [at[u] + at[v] for u, v in es]
    owner = {}

    def augment(i, seen):
        for slot in allowed[i]:
            if slot in seen:
                continue
            seen.add(slot)
            if slot not in owner or augment(owner[slot], seen):
                owner[slot] = i
                return True
        return False

    for i in range(len(es)):
        assert augment(i, set())
    assignment = {edge: slot for slot, edge in owner.items()}
    assert len(assignment) == len(es) == len(slots)
    D = nx.DiGraph()
    D.add_nodes_from(G)
    for i, (u, v) in enumerate(es):
        x = slots[assignment[i]][0]
        D.add_edge(x, v if x == u else u)
    assert all(D.out_degree(x) == r + (x == z) for x in G)
    if z is not None:
        assert nx.descendants(D, z) | {z} == set(G)
    return D


def matchings_on_edges(edges, size):
    for M in combinations(edges, size):
        if len({v for e in M for v in e}) == 2 * size:
            yield M


def all_matchings(vertices):
    """All matchings of the complete graph, including the empty matching."""
    vertices = tuple(vertices)
    if not vertices:
        yield ()
        return
    x, rest = vertices[0], vertices[1:]
    yield from all_matchings(rest)
    for i, y in enumerate(rest):
        for M in all_matchings(rest[:i] + rest[i + 1:]):
            yield ((x, y),) + M


def audit_slack_and_splits(G, r):
    for v in G:
        d = G.degree(v)
        if not r + 1 <= d <= 2 * r:
            continue
        t = d - r
        H = G.copy()
        H.remove_node(v)
        U, ec = counts(H)
        full = (1 << len(U)) - 1
        A = set(G[v])
        amask = sum(1 << i for i, x in enumerate(U) if x in A)
        sig = [r * s.bit_count() - ec[s] for s in range(full + 1)]
        assert sig[full] == t - 1
        for s in range(full):
            assert sig[s] >= max(0, (s & amask).bit_count() - r)
            STATS["one_vertex_slack_sets"] += 1
        if r >= 2:
            for x in combinations(A, 2):
                assert max(0, len(x) - r) == 0
            assert max(0, len(A) - r) == t > 0
        missing = [(x, y) for x, y in combinations(sorted(A), 2)
                   if not H.has_edge(x, y)]
        ix = {x: i for i, x in enumerate(U)}
        if t == 1:
            balanced = orientation(H, r, None)
            condensation = nx.condensation(balanced)
            sources = [set(condensation.nodes[x]["members"]) for x in condensation
                       if condensation.in_degree(x) == 0]
            assert all(A & S for S in sources)
            tight = [S for S in range(full + 1) if sig[S] == 0]
            for S in tight:
                for R in tight:
                    assert sig[S | R] == sig[S & R] == 0
            for x, y in missing:
                emask = (1 << ix[x]) | (1 << ix[y])
                hull = full
                for S in tight:
                    if S & emask == emask:
                        hull &= S
                C = {w for i, w in enumerate(U) if hull >> i & 1}
                reachable = nx.descendants(balanced, x) | nx.descendants(balanced, y) | {x, y}
                assert C == reachable
                assert (hull == full) == all({x, y} & S for S in sources)
                J = H.copy()
                J.add_edge(x, y)
                assert circuit(J.subgraph(C), r)
                for S in range(full + 1):
                    positive = ec[S] + int(S & emask == emask) > r * S.bit_count()
                    assert positive == (sig[S] == 0 and S & emask == emask)
                    if positive:
                        assert S & hull == hull
                STATS["canonical_one_edge_tight_hulls"] += 1
            if len(sources) == 2:
                for x in sorted(A & sources[0]):
                    for y in sorted(A & sources[1]):
                        assert not H.has_edge(x, y)
                        J = H.copy()
                        J.add_edge(x, y)
                        assert circuit(J, r)
                        STATS["two_source_spanning_completions"] += 1
        for F in combinations(missing, t):
            fmasks = [(1 << ix[x]) | (1 << ix[y]) for x, y in F]
            admissible = all(sum((s & e) == e for e in fmasks) <= sig[s]
                             for s in range(full))
            J = H.copy()
            J.add_edges_from(F)
            assert circuit(J, r) == admissible
            STATS["spanning_admissibility_equivalences"] += 1

        for z in G:
            if z == v:
                continue
            D = orientation(G, r, z)
            I, O = sorted(D.predecessors(v)), sorted(D.successors(v))
            assert len(I) == t and len(O) == r and not set(I) & set(O)
            simple_possible = False
            for heads in permutations(O, t):
                M = tuple(zip(I, heads))
                Dp = nx.MultiDiGraph()
                Dp.add_nodes_from(H)
                for x, y in D.edges():
                    if x != v and y != v:
                        Dp.add_edge(x, y, virtual=False)
                for x, y in M:
                    Dp.add_edge(x, y, virtual=True)
                assert all(Dp.out_degree(x) == r + (x == z) for x in H)
                J = nx.MultiGraph()
                J.add_nodes_from(H)
                J.add_edges_from((x, y) for x, y in Dp.edges())
                assert J.number_of_edges() == r * len(H) + 1
                C = nx.descendants(Dp, z) | {z}
                assert circuit(J.subgraph(C), r)
                jvs, jc = counts(J)
                cmask = sum(1 << i for i, x in enumerate(jvs) if x in C)
                for s, m in enumerate(jc):
                    assert m <= r * s.bit_count() + int(bool(s & (1 << jvs.index(z))))
                    if m > r * s.bit_count():
                        assert s & cmask == cmask
                q = sum(x in C and y in C for x, y in M)
                assert 1 <= q <= t
                assert G.subgraph(C).number_of_edges() == r * len(C) + 1 - q
                X = set(G) - C
                incident = sum(x in X or y in X for x, y in G.edges())
                assert incident == r * len(X) + q
                outgoing = [(x, y) for x, y in D.edges() if x in C and y not in C]
                assert len(outgoing) == q and all(y == v for _, y in outgoing)
                a = len(A & C)
                assert a >= 2 * q
                if C != set(H):
                    assert a <= r + q - 1
                    assert len(A - C) >= t - q + 1
                assert circuit(J, r) == (C == set(H))
                simple = all(not H.has_edge(x, y) for x, y in M)
                simple_possible |= simple
                if simple:
                    assert nx.Graph(J).number_of_edges() == J.number_of_edges()
                    assert len(C) >= 2 * r + 2
                    STATS["simple_oriented_splits"] += 1
                    if len(C) == 2 * r + 2 and q == 1:
                        assert G.subgraph(C).number_of_edges() == r * len(C)
                        STATS["one_virtual_edge_terminal_certificates"] += 1
                STATS["oriented_matching_splits"] += 1
            hall = True
            for mask in range(1 << len(I)):
                Z = {I[i] for i in range(len(I)) if mask >> i & 1}
                neigh = {y for y in O if any(not H.has_edge(x, y) for x in Z)}
                if len(neigh) < len(Z):
                    hall = False
                    Y = set(O) - neigh
                    assert len(Y) >= r - len(Z) + 1
                    assert all(H.has_edge(x, y) for x in Z for y in Y)
            assert simple_possible == hall
            STATS["nonedge_Hall_equivalences"] += 1


def audit_forward(G, r):
    for t in range(1, r + 1):
        for M in matchings_on_edges(list(G.edges()), t):
            ends = {x for e in M for x in e}
            for B in combinations(sorted(set(G) - ends), r - t):
                J = G.copy()
                J.remove_edges_from(M)
                v = max(G) + 1
                J.add_node(v)
                J.add_edges_from((v, x) for x in ends | set(B))
                assert J.degree(v) == r + t
                assert circuit(J, r)
                STATS["forward_matching_pinches"] += 1


def audit_elimination(G, r):
    vs, ec = counts(G)
    full = (1 << len(vs)) - 1
    f = [m - r * s.bit_count() for s, m in enumerate(ec)]
    profiles = {}
    for Z in range(full):
        U = full ^ Z
        p = {S: max(f[S | Y] for Y in submasks(Z)) for S in submasks(U)}
        profiles[Z] = p
        assert p[0] == 0 and p[U] == 1
        assert all(value <= 0 for S, value in p.items() if S != U)
        rho = {S: value - f[S] for S, value in p.items()}
        assert rho[0] == 0 and all(value >= 0 for value in rho.values())
        for S in p:
            for x in range(len(vs)):
                bit = 1 << x
                if U & bit and not S & bit:
                    assert rho[S] <= rho[S | bit]
            for R in p:
                assert p[S] + p[R] <= p[S | R] + p[S & R]
                assert rho[S] + rho[R] <= rho[S | R] + rho[S & R]
                STATS["elimination_supermodular_pairs"] += 1
        STATS["elimination_profiles"] += 1
    for Z, p in profiles.items():
        U = full ^ Z
        for W in submasks(U):
            if W == U:
                continue
            for S in submasks(U ^ W):
                direct = profiles[Z | W][S]
                iterated = max(p[S | Y] for Y in submasks(W))
                assert direct == iterated
                STATS["elimination_associativity_values"] += 1


def embedding_count(T, G, roots=(), allowed=None):
    tv, gv = list(T), list(G)
    index = {x: i for i, x in enumerate(tv)}
    edges = [(index[x], index[y]) for x, y in T.edges()]
    root_indices = [index[x] for x in roots]
    adj = {x: set(G[x]) for x in G}
    total = 0
    for image in permutations(gv, len(tv)):
        if allowed is not None and any(image[i] not in allowed for i in root_indices):
            continue
        if all(image[j] in adj[image[i]] for i, j in edges):
            total += 1
    return total


def audit_embedding_interfaces(G, r):
    for T in nx.nonisomorphic_trees(2 * r + 2):
        total = embedding_count(T, G)
        for v in G:
            if not r + 1 <= G.degree(v) <= 2 * r:
                continue
            H = G.copy()
            H.remove_node(v)
            rhs = embedding_count(T, H)
            for u in T:
                R = T.copy()
                R.remove_node(u)
                rhs += embedding_count(R, H, roots=list(T[u]), allowed=set(G[v]))
            assert rhs == total
            STATS["exact_adaptive_embedding_identities"] += 1


def audit_tree_forests():
    for N in (4, 6, 8, 10):
        for T in nx.nonisomorphic_trees(N):
            k = N - 1
            for u in T:
                roots = list(T[u])
                s = len(roots)
                R0 = T.copy()
                R0.remove_node(u)
                components = list(nx.connected_components(R0))
                assert len(components) == s
                assert all(len(set(roots) & C) == 1 for C in components)
                leaves = [x for x in roots if T.degree(x) == 1]
                for h in range(len(leaves) + 1):
                    for L in combinations(leaves, h):
                        R = R0.copy()
                        R.remove_nodes_from(L)
                        assert len(R) == k - h
                        assert R.number_of_edges() == k - s
                        assert nx.number_connected_components(R) == s - h
                        STATS["branch_and_sibling_leaf_interfaces"] += 1
                for Q in all_matchings(roots):
                    R = R0.copy()
                    R.add_edges_from(Q)
                    h = len(Q)
                    assert nx.is_forest(R)
                    assert len(R) == k and R.number_of_edges() == k - s + h
                    assert nx.number_connected_components(R) == s - h
                    assert s - h >= (s + 1) // 2
                    if nx.is_tree(R):
                        assert s <= 2
                    STATS["marked_forest_matching_interfaces"] += 1
                # A nonmatching star reconnects all the components for s>=3.
                Q = [(roots[0], x) for x in roots[1:]]
                R = R0.copy()
                R.add_edges_from(Q)
                assert nx.is_tree(R) and R.number_of_edges() == k - 1
                STATS["connected_branch_smoothings"] += 1


def audit_averaging(atlas):
    for N in (4, 6):
        for D in atlas:
            m = D.number_of_edges()
            if len(D) != N or 2 * m > N:
                continue
            for T in nx.nonisomorphic_trees(N):
                hist = Counter()
                tv = list(T)
                ix = {v: i for i, v in enumerate(tv)}
                te = [(ix[x], ix[y]) for x, y in T.edges()]
                for image in permutations(list(D)):
                    b = sum(D.has_edge(image[x], image[y]) for x, y in te)
                    hist[b] += 1
                assert sum(b * c for b, c in hist.items()) * N == 2 * m * factorial(N)
                nonstar = max(dict(T.degree()).values()) < N - 1
                if 2 * m < N or nonstar:
                    assert hist[0] > 0
                if 2 * m == N and nonstar:
                    assert any(b >= 2 and c > 0 for b, c in hist.items())
                STATS["averaging_histogram_audits"] += 1


def audit_join_terminal():
    for r in range(3, 41):
        a, b = r + 1, r * (r + 1) // 2 + 1
        n = a + b
        assert comb(a, 2) + a * b == r * n + 1
        assert n - 1 > 2 * r and r + 1 < 2 * r - 1
        for x in range(a + 1):
            for y in range(b + 1):
                if (x, y) == (a, b):
                    continue
                assert comb(x, 2) + x * y <= r * (x + y)
                STATS["join_family_induced_type_bounds"] += 1
        if r <= 5:
            G = nx.complete_graph(a)
            G.add_nodes_from(range(a, n))
            G.add_edges_from((x, y) for x in range(a) for y in range(a, n))
            for T in nx.nonisomorphic_trees(2 * r + 2):
                colors = nx.bipartite.color(T)
                sides = [[x for x in T if colors[x] == c] for c in (0, 1)]
                independent = sorted(max(sides, key=len))[:r + 1]
                other = sorted(set(T) - set(independent))
                image = dict(zip(other, range(a)))
                image.update(zip(independent, range(a, a + len(independent))))
                assert len(set(image.values())) == len(T)
                assert all(G.has_edge(image[x], image[y]) for x, y in T.edges())
                STATS["join_terminal_constructed_tree_copies"] += 1


def audit_rank_three():
    """Higher-rank operation audits, including a core-free path power.

    These are fixed theorem-check inputs, not a search for unresolved hosts.
    """
    for missing in (((0, 1), (2, 3), (4, 5)),
                    ((0, 1), (0, 2), (0, 3)),
                    ((0, 1), (1, 2), (2, 3))):
        G = nx.complete_graph(8)
        G.remove_edges_from(missing)
        assert circuit(G, 3)
        audit_slack_and_splits(G, 3)
        audit_forward(G, 3)
        audit_elimination(G, 3)
        STATS["rank_three_fixed_hosts"] += 1
    G = nx.Graph()
    G.add_nodes_from(range(11))
    G.add_edges_from((x, y) for x, y in combinations(range(11), 2) if y - x <= 4)
    assert circuit(G, 3)
    assert not nx.k_core(G, k=6)
    audit_slack_and_splits(G, 3)
    STATS["rank_three_fixed_hosts"] += 1


def main():
    spec = Path(__file__).with_name("Spec.lean")
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_HASH
    atlas = nx.graph_atlas_g()
    circuits = [(G, r) for G in atlas for r in (1, 2) if circuit(G, r)]
    for G, r in circuits:
        STATS[f"atlas_r{r}_circuits"] += 1
        audit_slack_and_splits(G, r)
        audit_forward(G, r)
        audit_elimination(G, r)
        audit_embedding_interfaces(G, r)
    audit_rank_three()
    audit_tree_forests()
    audit_averaging(atlas)
    audit_join_terminal()
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_HASH
    print("PASS: exact circuit, density-elimination, interface, and averaging audits")
    for key, value in sorted(STATS.items()):
        print(f"{key}: {value:,}")
    print(f"Spec.lean SHA-256 unchanged: {SPEC_HASH}")
    print("No general safe-split/tree-lifting theorem is asserted or tested as a premise.")


if __name__ == "__main__":
    main()
