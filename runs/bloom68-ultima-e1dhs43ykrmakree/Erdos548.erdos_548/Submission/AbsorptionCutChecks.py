#!/usr/bin/env python3
"""Exact cut/criticality audits. No tree-embedding backtracking or Lean changes.

Run: python3 Submission/AbsorptionCutChecks.py
Requires networkx and nauty-geng (available in the supplied environment).
The finite checks support, but do not replace, the proofs in AbsorptionCutFindings.md.
"""
from __future__ import annotations

from array import array
from collections import Counter
from itertools import combinations
import hashlib
import shutil
import subprocess
import time

import networkx as nx

SPEC_HASH = "674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103"
STATS = Counter()


def masks(G):
    assert set(G) == set(range(len(G)))
    return [sum(1 << w for w in G[v]) for v in G]


def vertices(S):
    while S:
        z = S & -S
        yield z.bit_length() - 1
        S ^= z


def induced_edges(adj, S):
    return sum((adj[v] & S).bit_count() for v in vertices(S)) // 2


def critical_brute(G, k):
    """Every proper induced subset, not just the vertex-deletion conditions."""
    n = len(G)
    adj = masks(G)
    full = (1 << n) - 1
    es = array("I", [0]) * (1 << n)
    for S in range(1, full + 1):
        z = S & -S
        v = z.bit_length() - 1
        R = S ^ z
        es[S] = es[R] + (adj[v] & R).bit_count()
        if S != full:
            STATS["proper subsets checked"] += 1
            if 2 * es[S] > (k - 1) * S.bit_count():
                return False
    return 2 * es[full] > (k - 1) * n


def cut_certificates(G, k, full_search=False):
    """Enumerate certificates, never embeddings. c is chosen optimally for A."""
    n = len(G)
    adj = masks(G)
    full = (1 << n) - 1
    H = [v for v in G if G.degree(v) >= k]
    if full_search:
        candidates = range(1, full)
    else:
        max_h = min(len(H), n - k)
        if all(G.has_edge(u, v) for u, v in combinations(H, 2)):
            max_h = min(max_h, max((G.degree(v) - k + 1 for v in H), default=0))
        candidates = (
            sum(1 << v for v in A)
            for h in range(1, max_h + 1)
            for A in combinations(H, h)
        )
    result = []
    for A in candidates:
        B = full ^ A
        if not B or any((adj[v] & B).bit_count() < k for v in vertices(A)):
            continue
        c0 = min((adj[v] & A).bit_count() for v in vertices(B))
        if c0 == 0:
            continue
        c = min(c0, k // 2)
        h, b = A.bit_count(), B.bit_count()
        eA = induced_edges(adj, A)
        q = sum((adj[v] & B).bit_count() for v in vertices(A))
        deficit2 = (k - 1) * h - 2 * eA
        gap2 = 2 * (q - c * b) - deficit2
        assert gap2 >= (k + 1) * h + 2 * eA - 2 * c * b
        # Independent arithmetic: the margin is the residual density shortfall.
        eta2 = 2 * G.number_of_edges() - (k - 1) * n
        assert gap2 == (k - 1 - 2 * c) * b + eta2 - 2 * induced_edges(adj, B)
        if full_search:
            # Check that taking the largest permitted c loses no certificate.
            possibilities = [
                2 * (q - cc * b) <= deficit2
                for cc in range(1, min(c0, k // 2) + 1)
            ]
            assert any(possibilities) == (gap2 <= 0)
        result.append((A, c0, c, gap2))
    return sorted(result)


def category(certs, k):
    if any(gap <= 0 for _, _, _, gap in certs):
        return "absorption"
    if any(c0 > k // 2 for _, c0, _, _ in certs):
        return "large-cross terminal only"
    return "cross but no budget" if certs else "no cross cut"


def audit_small_hosts():
    geng = shutil.which("nauty-geng") or shutil.which("geng")
    assert geng
    counts = Counter()
    examples = {}
    for n in range(4, 10):
        for k in range(3, n):
            m = (k - 1) * n // 2 + 1
            eta2 = 2 * m - (k - 1) * n
            mindeg = (k + eta2) // 2
            proc = subprocess.Popen(
                [geng, "-q", "-c", f"-d{mindeg}", str(n), f"{m}:{m}"],
                stdout=subprocess.PIPE,
            )
            assert proc.stdout is not None
            for line in proc.stdout:
                G = nx.from_graph6_bytes(line.strip())
                STATS["geng candidates"] += 1
                if not critical_brute(G, k):
                    continue
                STATS["critical hosts through order 9"] += 1
                certs = cut_certificates(G, k)
                if n <= 7:
                    assert certs == cut_certificates(G, k, full_search=True)
                    STATS["independent full-cut enumeration comparisons"] += 1
                label = category(certs, k)
                counts[n, k, label] += 1
                examples.setdefault(label, (n, k, line.strip().decode()))
                H = [v for v in G if G.degree(v) >= k]
                H_clique = all(G.has_edge(u, v) for u, v in combinations(H, 2))
                universal = any(G.degree(v) == n - 1 for v in G)
                if H_clique and max(dict(G.degree()).values()) <= k + 1 and not universal:
                    STATS["saturated-high-clique host audits"] += 1
                    for A, c0, c, gap in certs:
                        assert A.bit_count() == 2 and c0 == c == 1
                        assert all(G.degree(v) == k + 1 for v in vertices(A))
                        assert gap == 2 * (k + 4 - n)
                        STATS["sharp high-clique cut identities"] += 1
                if n == k + 1:
                    assert universal and label == "absorption"
                if n == k + 2 and k >= 4:
                    D = nx.complement(G)
                    small_component = any(len(C) <= 2 for C in nx.connected_components(D))
                    assert bool(certs) == small_component
                    assert bool(certs) == (label == "absorption")
                    STATS["order-k+2 complete classifications"] += 1
                if n == k + 3:
                    D = nx.complement(G)
                    if (all(D.degree(v) not in (0, 2) for v in D)
                            and all(len(C) != 2 for C in nx.connected_components(D))):
                        assert all(c0 == c == 1 and gap == 2 for _, c0, c, gap in certs)
                        assert label not in ("absorption", "large-cross terminal only")
                        STATS["complement unit-barrier shape audits"] += 1
            assert proc.wait() == 0
    print("SMALL CRITICAL HOSTS (all nonisomorphic, normalized surplus):")
    print("n k | absorption | large-cross-only | cross/no-budget | no-cross")
    for n, k in sorted({(n, k) for n, k, _ in counts}):
        row = [counts[n, k, s] for s in (
            "absorption", "large-cross terminal only", "cross but no budget", "no cross cut")]
        print(n, k, *row, sep=" ")
    print("Totals by certificate status:", dict(sum((Counter({s: c}) for (_, _, s), c in counts.items()), Counter())))
    print("First graph6 examples:", examples)


def unit_budget_host(t):
    assert t >= 2
    k = 4 * t + 1
    groups = [list(range(t)), list(range(t, 2 * t)), list(range(2 * t, 3 * t - 1))]
    W = list(range(k))
    P = list(range(k, k + 3))
    G = nx.complete_graph(k)
    G.add_nodes_from(P)
    G.add_edges_from(combinations(P, 2))
    for i, p in enumerate(P):
        for j, X in enumerate(groups):
            if i != j:
                G.add_edges_from((p, x) for x in X)
    return G, k, W, P, groups


def orientation_certificate(G, r, root):
    """Full criticality certificate: r-out everywhere, root r+1, root reaches all."""
    edges = list(G.edges())
    source = ("source",)
    sink = ("sink",)
    F = nx.DiGraph()
    for i, (u, v) in enumerate(edges):
        enode = ("edge", i)
        F.add_edge(source, enode, capacity=1)
        F.add_edge(enode, ("v", u), capacity=1)
        F.add_edge(enode, ("v", v), capacity=1)
    for v in G:
        F.add_edge(("v", v), sink, capacity=r + (v == root))
    value, flow = nx.maximum_flow(F, source, sink)
    assert value == len(edges)
    O = nx.DiGraph()
    O.add_nodes_from(G)
    for i, (u, v) in enumerate(edges):
        if flow["edge", i]["v", u] == 1:
            O.add_edge(u, v)
        else:
            assert flow["edge", i]["v", v] == 1
            O.add_edge(v, u)
    verify_orientation(G, O, r, root)
    return O


def verify_orientation(G, O, r, root):
    assert len(O.edges()) == G.number_of_edges()
    assert all(O.has_edge(u, v) != O.has_edge(v, u) for u, v in G.edges())
    assert all(O.out_degree(v) == r + (v == root) for v in G)
    assert len(nx.descendants(O, root)) == len(G) - 1
    # For a proper S containing root, reachability supplies an outgoing arc;
    # otherwise the outdegree sum itself bounds e(S). This checks ALL S.
    STATS["full criticality orientation certificates"] += 1


def verify_embedding(T, G, phi):
    assert set(phi) == set(T)
    assert len(set(phi.values())) == len(T)
    assert set(phi.values()) <= set(G)
    assert all(G.has_edge(phi[u], phi[v]) for u, v in T.edges())
    STATS["constructive tree embeddings checked"] += 1


def one_leaf_clique_embedding(T, G, W, outside):
    leaf = next(v for v in T if T.degree(v) == 1)
    parent = next(iter(T[leaf]))
    parent_image = next(v for v in W if G.has_edge(outside, v))
    phi = {leaf: outside, parent: parent_image}
    phi.update(zip((v for v in T if v not in phi), (v for v in W if v != parent_image)))
    verify_embedding(T, G, phi)


def audit_unit_family():
    for t in range(2, 21):
        G, k, W, P, groups = unit_budget_host(t)
        assert len(G) == k + 3
        assert G.number_of_edges() == 2 * t * len(G) + 1
        assert min(dict(G.degree()).values()) == 2 * t + 1
        assert max(dict(G.degree()).values()) == k + 1
        certs = cut_certificates(G, k)
        assert len(certs) == sum(len(groups[i]) * len(groups[j]) for i, j in combinations(range(3), 2))
        assert all(c0 == c == 1 and gap == 2 for _, c0, c, gap in certs)
        STATS["unit-budget family cuts checked"] += len(certs)
        if t <= 4:
            assert critical_brute(G, k)
            assert certs == cut_certificates(G, k, full_search=True)
        if t <= 10:
            orientation_certificate(G, 2 * t, P[0])
        if t <= 3:
            for T in nx.nonisomorphic_trees(k + 1):
                one_leaf_clique_embedding(T, G, W, P[0])
    print("Unit-budget family: t=2..20; all eligible cuts have deficit gap exactly 1.")
    # A genuine critical equality case at n=k+4, not just a formal identity.
    G, k, W, P, groups = unit_budget_host(2)
    r = (k - 1) // 2
    Z = sorted(set(W) - set().union(*map(set, groups)))
    M = [(Z[0], Z[1]), (Z[2], Z[3]), (P[0], P[1]), (P[2], groups[0][0])]
    assert len(M) == r and len({z for e in M for z in e}) == 2 * r
    assert all(G.has_edge(u, v) for u, v in M)
    old_degrees = dict(G.degree())
    new_vertex = len(G)
    G.remove_edges_from(M)
    G.add_edges_from((new_vertex, z) for e in M for z in e)
    assert all(G.degree(v) == d for v, d in old_degrees.items())
    assert G.degree(new_vertex) == 2 * r and critical_brute(G, k)
    certs = cut_certificates(G, k)
    assert len(certs) == 2 and all(c0 == c == 1 and gap == 0 for _, c0, c, gap in certs)
    STATS["critical zero-gap equality cuts"] += len(certs)
    print("Matching-cone equality example: k=9, n=13, two verified absorbing pairs of margin 0.")


def regular_core_host(r, flavor):
    assert r >= 3 and flavor in ("cliques", "rook")
    U = list(range(r))
    V = list(range(r, 2 * r))
    p, q = 2 * r, 2 * r + 1
    def w(b, i, j):
        return 2 * r + 2 + b * r * r + i * r + j
    G = nx.Graph()
    G.add_nodes_from(range(2 * r * r + 2 * r + 2))
    G.add_edges_from((u, v) for u in U for v in V)
    G.add_edges_from((p, v) for v in V)
    G.add_edges_from((q, u) for u in U)
    G.add_edge(p, q)
    for b in range(2):
        for i in range(r):
            for j in range(r):
                G.add_edge(w(b, i, j), b * r + i)
    if flavor == "cliques":
        for j in range(r):
            G.add_edges_from(combinations([w(b, i, j) for b in range(2) for i in range(r)], 2))
    else:
        for b in range(2):
            for i in range(r):
                G.add_edges_from(combinations([w(b, i, j) for j in range(r)], 2))
            for j in range(r):
                G.add_edges_from(combinations([w(b, i, j) for i in range(r)], 2))
        G.add_edges_from((w(0, i, j), w(1, i, j)) for i in range(r) for j in range(r))
    return G, U, V, p, q, w


def core_orientation(G, U, V, p, q, r):
    Q = G.copy()
    Q.remove_nodes_from([p, q])
    assert nx.is_connected(Q)
    assert all(Q.degree(v) == 2 * r for v in Q)
    O = nx.DiGraph()
    O.add_nodes_from(G)
    O.add_edges_from(nx.eulerian_circuit(Q))
    O.add_edges_from((p, v) for v in V)
    O.add_edges_from((q, u) for u in U)
    O.add_edge(p, q)
    verify_orientation(G, O, r, p)


def two_leaf_clique_embedding(T, G, U, V, w, r):
    k = 2 * r + 1
    center = next((v for v in T if T.degree(v) == k), None)
    if center is not None:
        phi = {center: U[0]}
        phi.update(zip((v for v in T if v != center), G[U[0]]))
    else:
        leaves = [v for v in T if T.degree(v) == 1]
        l1, l2 = next((x, y) for x, y in combinations(leaves, 2)
                      if next(iter(T[x])) != next(iter(T[y])))
        C = [w(b, i, 0) for b in range(2) for i in range(r)]
        phi = dict(zip((v for v in T if v not in (l1, l2)), C))
        label = {w(b, i, 0): b * r + i for b in range(2) for i in range(r)}
        phi[l1] = label[phi[next(iter(T[l1]))]]
        phi[l2] = label[phi[next(iter(T[l2]))]]
    verify_embedding(T, G, phi)


def nonspider_tree(r):
    T = nx.path_graph(2 * r - 1)
    for extra, parent in zip(range(2 * r - 1, 2 * r + 2), (1, 2, 3)):
        T.add_edge(extra, parent)
    return T


def explicit_rook_embedding(r, G, w):
    T = nonspider_tree(r)
    assert T.number_of_edges() == 2 * r + 1
    assert max(dict(T.degree()).values()) == 3
    assert sum(T.degree(v) == 3 for v in T) == 3
    colors = nx.bipartite.color(T)
    assert sorted(Counter(colors.values()).values()) == [r, r + 2]
    assert all(max(T.degree(v) for v in T if colors[v] == b) == 3 for b in (0, 1))
    path = [w(0, 0, j) for j in range(r)] + [w(0, 1, j) for j in range(r - 1, 0, -1)]
    phi = dict(enumerate(path))
    phi[2 * r - 1] = w(0, 2, 1)
    phi[2 * r] = w(0, 2, 2)
    phi[2 * r + 1] = w(0, 1, 0) if r == 3 else w(0, 2, 3)
    verify_embedding(T, G, phi)


def audit_rook_relation(G, U, V, p, q, w, r):
    adj = masks(G)
    canonical = [set(U) | {p}, set(V) | {q}]
    for b in range(2):
        for i in range(r):
            canonical.append({b * r + i} | {w(b, i, j) for j in range(r)})
        for j in range(r):
            canonical.append({w(b, i, j) for i in range(r)})
    J = nx.Graph()
    J.add_nodes_from(G)
    max_codeg = 0
    min_diff = len(G)
    for u, v in combinations(G, 2):
        codeg = (adj[u] & adj[v]).bit_count()
        max_codeg = max(max_codeg, codeg)
        min_diff = min(min_diff, (adj[u] ^ adj[v]).bit_count())
        if codeg >= 3:
            J.add_edge(u, v)
            assert any({u, v} <= C for C in canonical)
        STATS["rook neighborhood-pair audits"] += 1
    assert max_codeg == r + 1 and min_diff == r
    for C in nx.find_cliques(J):
        if len(C) >= 2:
            assert any(set(C) <= D for D in canonical)
        assert len(C) <= r + 1
        STATS["rook codegree-relation maximal cliques"] += 1
    for C in canonical[2:]:
        assert all(len(set(G[x]) & C) <= 1 for x in G if x not in C)
    L, R = canonical[:2]
    assert all(len(set(G[x]) & L) <= 1 for x in G if x not in R)
    assert all(len(set(G[x]) & R) <= 1 for x in G if x not in L)
    # These exact relations certify the no-uniform-Hall/no-near-clique lemmas;
    # no search failing to find an embedding is used as evidence for them.
    assert nx.graph_clique_number(G) == r + 1
    STATS["rook obstruction hosts"] += 1


def audit_regular_core_families():
    for flavor in ("cliques", "rook"):
        for r in range(3, 13):
            G, U, V, p, q, w = regular_core_host(r, flavor)
            k = 2 * r + 1
            H = set(U) | set(V)
            assert G.number_of_edges() == r * len(G) + 1
            assert {v for v in G if G.degree(v) >= k} == H
            assert all(G.degree(v) == k for v in H)
            assert min(dict(G.degree()).values()) == r + 1
            assert all(G.has_edge(u, v) for u in U for v in V)
            assert not (set(G[p]) & set(U)) and not (set(G[q]) & set(V))
            assert all(set(G[v]) & H for v in G if v not in H)
            assert not nx.is_bipartite(G)
            # No cut: eligible A is an independent subset of H, hence lies
            # wholly in U or V, and misses p or q respectively.
            if r <= 5:
                assert not cut_certificates(G, k)
            # No exact one-apex CL certificate on ANY subgraph for Delta(T)<=r.
            for s in H:
                low = q if s in U else p
                assert G.has_edge(s, low) and G.degree(low) - 1 == r < k - r
            core_orientation(G, U, V, p, q, r)
            if flavor == "cliques" and r <= 6:
                for T in nx.nonisomorphic_trees(k + 1):
                    two_leaf_clique_embedding(T, G, U, V, w, r)
            if flavor == "rook":
                audit_rook_relation(G, U, V, p, q, w, r)
                explicit_rook_embedding(r, G, w)
    print("Regular-core families: r=3..12, full oriented criticality certificates,")
    print("  no-cut/type certificates, all-subgraph CL obstruction, and explicit embeddings.")
    print("Rook family: max codegree r+1, min neighborhood difference r, clique number r+1;")
    print("  codegree>=3 relation and all outside-neighbor bounds independently audited.")


def main():
    start = time.time()
    with open("Submission/Spec.lean", "rb") as f:
        assert hashlib.sha256(f.read()).hexdigest() == SPEC_HASH
    audit_small_hosts()
    audit_unit_family()
    audit_regular_core_families()
    print("CHECK COUNTS:")
    for key, value in sorted(STATS.items()):
        print(f"  {key}: {value}")
    with open("Submission/Spec.lean", "rb") as f:
        assert hashlib.sha256(f.read()).hexdigest() == SPEC_HASH
    print("PASS; Spec.lean unchanged; elapsed seconds:", round(time.time() - start, 2))


if __name__ == "__main__":
    main()
