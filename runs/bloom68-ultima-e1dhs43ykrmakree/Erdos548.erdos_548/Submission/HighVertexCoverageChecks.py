#!/usr/bin/env python3
"""Constructive audits for HighVertexCoverageFindings.md.

No random graph enumeration, ES oracle, or Lean edits.  The only negative
criticality test is an exact integer max-closure calculation.  General claims
are proved in the report; these checks audit the constructions and formulas.
"""
from __future__ import annotations

from collections import Counter
from itertools import combinations
from pathlib import Path
import hashlib
import networkx as nx

from CommonMarkedForestChecks import compile_components, common_marked_forest

ST = Counter()
HERE = Path(__file__).resolve().parent
SPEC_SHA = "674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103"


def check_copy(T, G, f, root=None):
    assert set(f) == set(T)
    assert len(set(f.values())) == len(T)
    assert set(f.values()) <= set(G)
    assert all(G.has_edge(f[u], f[v]) for u, v in T.edges())
    if root is not None:
        u, s = root
        assert f[u] == s
    ST["verified full injective copies"] += 1


def small_color(T):
    color = nx.bipartite.color(T)
    A = {u for u in T if color[u] == 0}
    B = set(T) - A
    return (A, B) if len(A) <= len(B) else (B, A)


def assign(domain, positions, u=None, s=None):
    domain, positions = set(domain), set(positions)
    assert len(domain) <= len(positions)
    f = {}
    if u is not None:
        assert u in domain and s in positions
        f[u] = s
        domain.remove(u)
        positions.remove(s)
    f.update(zip(sorted(domain), sorted(positions)))
    return f


def greedy_tree(T, G, u, s):
    f = {u: s}
    for p, v in nx.bfs_edges(T, u):
        candidates = set(G[f[p]]) - set(f.values())
        assert candidates, (p, v, f)
        f[v] = min(candidates)
    return f


def forest_copy(F, G, B):
    order = sorted(B)
    pos = {v: i for i, v in enumerate(order)}
    adj = [sum(1 << pos[w] for w in G[v] if w in pos) for v in order]
    assert len(B) >= len(F)
    assert all(a.bit_count() >= F.number_of_edges() for a in adj)
    marks = {min(C) for C in nx.connected_components(F)}
    components = compile_components(F, marks)
    all_vertices = (1 << len(order)) - 1
    ff = common_marked_forest(adj, all_vertices, all_vertices, components)
    ST["constructive CL forest calls"] += 1
    return {v: order[x] for v, x in ff.items()}


def independent_selection(T, A, h, p):
    assert 1 <= h < len(A) and p in A and T.degree(p) >= 2
    I = {v for v in A if T.degree(v) >= 2}
    if len(I) >= h:
        U = {p} | set(sorted(I - {p})[:h - 1])
    else:
        U = I | set(sorted(A - I)[:h - len(I)])
    assert len(U) == h and p in U
    assert sum(T.degree(v) for v in U) >= 2*h
    assert T.subgraph(U).number_of_edges() == 0
    return U


def multipartite_copy(G, parts, T, p, s):
    k, n = len(T) - 1, len(G)
    assert 2*G.number_of_edges() > (k-1)*n and G.degree(s) >= k
    A, B = small_color(T)
    assert p in A and T.degree(p) >= 2
    t = n-k
    high_parts = [C for C in parts if len(C) <= t]
    H = set().union(*high_parts)
    assert H == {v for v in G if G.degree(v) >= k}
    if len(H) >= len(A):
        first = next(C for C in high_parts if s in C)
        X = set(first)
        for C in high_parts:
            if len(X) >= len(A):
                break
            X |= C
        assert len(A) <= len(X) <= len(A)+t-1
        assert s in X
        f = assign(A, X, p, s)
        f.update(assign(B, set(G)-X))
        ST["multipartite grouping, prescribed high vertex"] += 1
    else:
        h = len(H)
        L = set(G)-H
        assert all(len(C) <= t+h for C in parts if C <= L)
        assert min(len(set(G[v]) & L) for v in L) >= k-2*h
        U = independent_selection(T, A, h, p)
        F = T.subgraph(set(T)-U).copy()
        f = forest_copy(F, G, L)
        f.update(assign(U, H, p, s))
        ST["multipartite deficit branch, prescribed high vertex"] += 1
    check_copy(T, G, f, (p, s))
    return f


def partitions(n, least=1):
    if not n:
        yield ()
    else:
        for a in range(least, n+1):
            for tail in partitions(n-a, a):
                yield (a,) + tail


def multipartite_audit():
    # A proof audit on a modest, explicit algebraic host class, not a search
    # for general critical counterexamples.
    trees = {k: list(nx.nonisomorphic_trees(k+1)) for k in range(2, 9)}
    for n in range(3, 13):
        for sizes in partitions(n):
            if len(sizes) < 2:
                continue
            G = nx.complete_multipartite_graph(*sizes)
            parts, start = [], 0
            for c in sizes:
                parts.append(set(range(start, start+c)))
                start += c
            for k in range(2, min(8, n-1)+1):
                if 2*G.number_of_edges() <= (k-1)*n:
                    continue
                high = [v for v in G if G.degree(v) >= k]
                for T in trees[k]:
                    A, _ = small_color(T)
                    # Any smaller-color nonleaf can be retained. Exercise all
                    # of them and every high host vertex, not just maxima.
                    for p in sorted(v for v in A if T.degree(v) >= 2):
                        for s in high:
                            multipartite_copy(G, parts, T, p, s)
    assert ST["multipartite deficit branch, prescribed high vertex"] > 0


def clique_join(r):
    # K_r joined to q independent K_2 modules, q = r(r+1)/2+1.
    q = r*(r+1)//2 + 1
    G = nx.complete_graph(r)
    S = set(range(r))
    modules = []
    start = r
    for _ in range(q):
        C = {start, start+1}
        start += 2
        G.add_edge(*sorted(C))
        G.add_edges_from((s, c) for s in S for c in C)
        modules.append(C)
    assert G.number_of_edges() == r*len(G)+1
    return G, S, modules


def clique_join_copy(G, S, modules, T, p, s):
    k, a = len(T)-1, len(S)
    A, B = small_color(T)
    assert G.degree(s) >= k
    if s not in S:
        C = next(C for C in modules if s in C)
        K = C | S
        assert len(K) >= k+1
        f = assign(T, K, p, s)
        ST["high wing vertex in a complete block"] += 1
    elif a >= len(A):
        f = assign(A, S, p, s)
        f.update(assign(B, set(G)-set(f.values())))
        ST["clique-join direct branch"] += 1
    else:
        assert all(len(C)-1 >= k-2*a for C in modules)
        U = independent_selection(T, A, a, p)
        f = forest_copy(T.subgraph(set(T)-U).copy(), G, set(G)-S)
        f.update(assign(U, S, p, s))
        ST["clique-join forest branch"] += 1
    check_copy(T, G, f, (p, s))


def clique_join_audit():
    for r in range(2, 6):
        k = 2*r+1
        G, S, modules = clique_join(r)
        # An exact coordinate check of all induced-subset maxima. For x<r,
        # every nonempty module choice has nonpositive contribution. At x=r,
        # a full module contributes 1, a proper module contributes 0.
        for x in range(r):
            assert x*(x-1)//2-r*x <= 0
            assert max(0, x-r, 1+2*x-2*r) == 0
        assert len(modules)-r*(r+1)//2 == 1
        ST["clique-join criticality certificates"] += 1
        for T in nx.nonisomorphic_trees(k+1):
            A, _ = small_color(T)
            p = min(v for v in A if T.degree(v) >= 2)
            for s in S:
                clique_join_copy(G, S, modules, T, p, s)
    # Also exercise the high vertex in a wing case.
    for k in range(3, 9):
        G = nx.complete_graph(k+1)
        S, modules = {0}, [set(range(1, k+1))]
        for T in nx.nonisomorphic_trees(k+1):
            A, _ = small_color(T)
            p = min(v for v in A if T.degree(v) >= 2)
            for s in G:
                clique_join_copy(G, S, modules, T, p, s)


def colored_leaf_copy(G, T, s):
    k = len(T)-1
    A, B = small_color(T)
    assert min(dict(G.degree()).values()) >= max(len(A), len(B)-1)
    assert G.degree(s) >= k
    ell = min(v for v in B if T.degree(v) == 1)
    p = next(iter(T[ell]))
    R = T.copy()
    R.remove_node(ell)
    # BFS automatically respects whichever host bipartition contains s.
    f = greedy_tree(R, G, p, s)
    f[ell] = min(set(G[s])-set(f.values()))
    check_copy(T, G, f, (p, s))
    ST["bipartite leaf-deletion coverage"] += 1


def bipartite_audit():
    for r in range(2, 5):
        k, q = 2*r+1, 2*r+1
        G = nx.complete_bipartite_graph(q, q)
        G.remove_edges_from((i, q+i) for i in range(1, q))
        # Connected 2r-regular graph plus one missing edge: full r-critical.
        assert G.number_of_edges() == r*len(G)+1
        for T in nx.nonisomorphic_trees(k+1):
            for s in (0, q):
                colored_leaf_copy(G, T, s)
    # The old bipartite radius-two degree obstruction has delta=3 and k=5.
    # Check the new local-degree lemma without modifying that construction.
    from AdjacentRootFlexibilityChecks import graph32_bipartite
    G, _, _, _, _, _, _ = graph32_bipartite()
    for T in nx.nonisomorphic_trees(6):
        A, B = small_color(T)
        if max(len(A), len(B)-1) <= 3:
            for s in G:
                if G.degree(s) >= 5:
                    colored_leaf_copy(G, T, s)


def even_spider(parts):
    T = nx.Graph()
    T.add_node(0)
    nxt = 1
    for h in parts:
        prev = 0
        for _ in range(2*h):
            T.add_edge(prev, nxt)
            prev = nxt
            nxt += 1
    return T


def spider_exception_audit():
    # Audit the precise new step in the literature corollary: its exceptional
    # complete bipartite block still contains the specified high vertex.
    for m in range(2, 10):
        G = nx.complete_bipartite_graph(m+1, m)
        X, Y = set(range(m+1)), set(range(m+1, 2*m+1))
        for parts in partitions(m):
            T = even_spider(parts)
            A, B = small_color(T)
            assert len(A) == m and len(B) == m+1 and 0 in B
            for s in G:
                if s in X:
                    u = 0
                    f = assign(B, X, u, s)
                    f.update(assign(A, Y))
                else:
                    u = min(A)
                    f = assign(A, Y, u, s)
                    f.update(assign(B, X))
                check_copy(T, G, f, (u, s))
                ST["spider exceptional-block coverage"] += 1
    # Exact half-integral critical examples in the low-Delta boundary regime.
    for m in range(3, 11):
        k, b = 2*m, m*(2*m-1)+1
        G = nx.complete_bipartite_graph(m, b)
        T = even_spider((1,)*m)
        assert 2*G.number_of_edges()-(k-1)*len(G) == 1
        for x in range(m+1):
            for y in range(b+1):
                if (x, y) != (m, b):
                    assert 2*x*y <= (k-1)*(x+y)
        A, B = small_color(T)
        assert len(A) == m and len(B) == m+1
        for s in range(m):
            for u in A:
                f = assign(A, set(range(m)), u, s)
                f.update(assign(B, set(range(m, m+b))))
                check_copy(T, G, f, (u, s))
                ST["low-Delta internal-role coverage in critical bicliques"] += 1
        ST["half-integral critical biclique certificates"] += 1


def uniform_star_tree(ell, t):
    T = nx.Graph()
    T.add_node(0)
    hubs, leaves = list(range(1, ell+1)), {}
    nxt = ell+1
    for u in hubs:
        T.add_edge(0, u)
        leaves[u] = list(range(nxt, nxt+t))
        T.add_edges_from((u, v) for v in leaves[u])
        nxt += t
    assert nx.is_tree(T) and T.number_of_edges() == ell*(t+1)
    return T, hubs, leaves


def two_wing(ell, t):
    assert ell >= 3 and ell % 2 == 1 and t >= ell
    a, b = (ell+1)*t//2-1, (ell-1)*t
    G = nx.Graph()
    G.add_node(0)
    wings, nxt = [], 1
    for _ in range(2):
        A = list(range(nxt, nxt+b)); nxt += b
        B = list(range(nxt, nxt+a)); nxt += a
        G.add_edges_from((0, x) for x in A)
        G.add_edges_from((x, y) for x in A for y in B)
        wings.append((A, B))
    return G, wings


def repair_copy(G, wings, ell, t, wing, endpoint, outside, kind):
    T, hubs, leaves = uniform_star_tree(ell, t)
    A, B = wings[wing]
    A2, B2 = wings[1-wing]
    assert outside not in {0} | set(A) | set(B) | set(A2) | set(B2)
    assert G.has_edge(endpoint, outside)
    f = {}
    if kind == "A":
        assert endpoint in A
        f[0] = 0
        q = (ell+1)//2
        images = [endpoint] + [x for x in A if x != endpoint][:q-1]
        f.update(zip(hubs[:q], images))
        f.update(zip(hubs[q:], A2))
        f[leaves[hubs[0]][0]] = outside
        slots = [v for u in hubs[:q] for v in leaves[u] if v not in f]
        assert len(slots) == len(B)
        f.update(zip(slots, B))
        slots2 = [v for u in hubs[q:] for v in leaves[u]]
        f.update(zip(slots2, B2))
        root = (0, 0)
    elif kind == "B":
        assert endpoint in B
        f[hubs[0]] = 0
        f[0] = A[0]
        images = [endpoint] + [x for x in B if x != endpoint][:ell-2]
        f.update(zip(hubs[1:], images))
        f[leaves[hubs[1]][0]] = outside
        slots = [v for u in hubs[1:] for v in leaves[u] if v not in f]
        assert len(slots) == len(A)-1
        f.update(zip(slots, A[1:]))
        f.update(zip(leaves[hubs[0]], A2))
        root = (hubs[0], 0)
    else:
        raise ValueError(kind)
    check_copy(T, G, f, root)
    ST["fresh-boundary-edge adaptive repairs"] += 1
    return f


def apex_only_extension_copy(G, wings, ell, t, w):
    T, hubs, leaves = uniform_star_tree(ell, t)
    old = {0} | set().union(*(set(A) | set(B) for A, B in wings))
    assert w not in old and G.has_edge(0, w)
    choices = set(G[w])-{0}
    assert choices.isdisjoint(old) and len(choices) >= t
    f = {0: 0, hubs[0]: w}
    f.update(zip(leaves[hubs[0]], sorted(choices)))
    p = (ell-1)//2
    for i, (A, B) in enumerate(wings):
        these = hubs[1+i*p:1+(i+1)*p]
        f.update(zip(these, A))
        slots = [v for u in these for v in leaves[u]]
        f.update(zip(slots, B))
    check_copy(T, G, f, (0, 0))
    ST["apex-only connected-extension repairs"] += 1


def two_wing_audit():
    for ell in (3, 5, 7, 9):
        for t in range(ell, ell+7):
            k, a, b = ell*(t+1), (ell+1)*t//2-1, (ell-1)*t
            assert 2*b >= k
            assert min(a+1, b) >= (k+1)//2
            assert max(ell, t+1) <= k//2
            assert ((ell+1)//2)*t == a+1
            assert (ell-1)*t+1 == b+1
            assert ell*t > max(a, b)
            D4 = (ell*ell-ell+2)*t*t + (3*ell*ell-6*ell+1)*t - 2*(ell-1)
            assert D4 == 2*(k-1)*(a+b)-4*b*(a+1) and D4 > 0
            ST["two-wing all-role obstruction and charge identities"] += 1
            G, wings = two_wing(ell, t)
            w = max(G)+1
            for wing in (0, 1):
                for kind, j in (("A", 0), ("B", 1)):
                    endpoint = wings[wing][j][0]
                    G.add_edge(endpoint, w)
                    repair_copy(G, wings, ell, t, wing, endpoint, w, kind)
                    G.remove_node(w)
            # Extension through s only: the external component is a clique,
            # so its vertex w has at least t other fresh neighbors.
            fresh = list(range(w, w+t+2))
            G.add_edges_from(combinations(fresh, 2))
            G.add_edge(0, w)
            apex_only_extension_copy(G, wings, ell, t, w)


def critical_trap(ell):
    assert ell >= 3 and ell % 2 == 1
    t, k = ell+1, ell*(ell+2)
    r, b = (k-1)//2, ell*ell-1
    h = (r+1)//2
    G0, wings = two_wing(ell, t)
    D = nx.DiGraph()
    D.add_nodes_from(G0)
    for A, B in wings:
        assert len(B) == r
        for j, x in enumerate(A):
            if j < h:
                D.add_edge(0, x)
                D.add_edges_from((x, y) for y in B)
            else:
                D.add_edge(x, 0)
                reverse = B[(j-h) % r]
                D.add_edges_from((x, y) for y in B if y != reverse)
                D.add_edge(reverse, x)
    assert nx.Graph(D).edges() == G0.edges()
    nxt, ports, parent = len(G0), [], {}
    for _, B in wings:
        for y in B:
            need = r-D.out_degree(y)
            assert need > 0
            for _ in range(need):
                D.add_edge(y, nxt)
                ports.append(nxt)
                parent[nxt] = y
                nxt += 1
    assert len(ports) == 2*r*r-2*b+r+1
    assert len(ports) > 2*r
    for i, x in enumerate(ports):
        for j in range(1, r+1):
            D.add_edge(x, ports[(i+j) % len(ports)])
    G = nx.Graph(D)
    assert G.number_of_edges() == D.number_of_edges()
    assert all(D.out_degree(v) == r+(v == 0) for v in D)
    assert nx.descendants(D, 0) == set(D)-{0}
    assert len(G) == 2*r*r+3*r+2
    assert G.number_of_edges() == r*len(G)+1
    assert G.degree(0) == 2*b >= k
    assert all(G.degree(v) < G.degree(0) for v in G if v != 0)
    assert G.subgraph(G0).number_of_edges() == G0.number_of_edges()
    assert all(G.has_edge(u, v) for u, v in G0.edges())
    ST["root-reachable full critical orientation certificates"] += 1
    # The boundary edge forces a HUB role. The center is still impossible:
    # N(s) consists of the A classes, and every such vertex has exactly its
    # r B neighbors and s, so the old center-role capacity obstruction persists.
    p0 = ports[0]
    y = parent[p0]
    repair_copy(G, wings, ell, t, 0, y, p0, "B")
    T, hubs, leaves = uniform_star_tree(ell, t)
    assert max(dict(T.degree()).values()) == ell+2 <= r
    ell0 = leaves[hubs[0]][0]
    R = T.copy(); R.remove_node(ell0)
    f = greedy_tree(R, G.subgraph(ports), hubs[0], p0)
    f[ell0] = y
    check_copy(T, G, f)
    assert 0 not in f.values()
    ST["ordinary copies avoiding the unique maximum"] += 1
    return G, r


def even_critical_trap():
    """k=12, Delta(T)=4, and a doubled-edge quota certificate at eta=1/2."""
    ell, t, k = 3, 3, 12
    G0, wings = two_wing(ell, t)
    D = nx.DiGraph()
    D.add_nodes_from(G0)

    def arc(u, v, weight):
        assert not D.has_edge(u, v)
        D.add_edge(u, v, weight=weight)

    for A, B in wings:
        for x in A:
            arc(0, x, 1)
            arc(x, 0, 1)
            for y in B:
                arc(x, y, 2)
    P = list(range(len(G0), len(G0)+60))
    half_indices = list(range(5)) + list(range(30, 35))
    full_indices = [i for i in range(60) if i not in half_indices]
    B_all = wings[0][1] + wings[1][1]
    for j, y in enumerate(B_all):
        for i in full_indices[5*j:5*j+5]:
            arc(y, P[i], 2)
        z = P[half_indices[j]]
        arc(y, z, 1)
        arc(z, y, 1)
    # Fifth power of C_60, plus the antipodal matching except for five pairs.
    for i in range(60):
        for h in range(1, 6):
            u, v = P[i], P[(i+h) % 60]
            arc(u, v, 1)
            arc(v, u, 1)
    for i in range(5, 30):
        arc(P[i], P[i+30], 1)
        arc(P[i+30], P[i], 1)
    G = nx.Graph(D)
    for u, v in G.edges():
        weight = (D[u][v]['weight'] if D.has_edge(u, v) else 0)
        weight += (D[v][u]['weight'] if D.has_edge(v, u) else 0)
        assert weight == 2
    assert all(D.out_degree(v, weight='weight') == 11+(v == 0) for v in D)
    assert nx.descendants(D, 0) == set(G)-{0}
    assert len(G) == 83 and G.number_of_edges() == 457 and G.degree(0) == 12
    assert min(dict(G.degree()).values()) == 6
    assert G.subgraph(G0).number_of_edges() == G0.number_of_edges()
    ST['doubled-quota full critical orientation certificates'] += 1
    repair_copy(G, wings, ell, t, 0, B_all[0], P[0], 'B')
    T, hubs, leaves = uniform_star_tree(ell, t)
    f = {0: P[0], hubs[0]: P[1], hubs[1]: P[2], hubs[2]: P[3]}
    leaf_indices = ([56, 57, 58], [59, 4, 7], [5, 6, 8])
    for u, indices in zip(hubs, leaf_indices):
        f.update(zip(leaves[u], [P[i] for i in indices]))
    check_copy(T, G, f)
    assert 0 not in f.values() and max(dict(T.degree()).values()) == 4
    ST['ordinary copies avoiding the marked high vertex, even parameter'] += 1
    # Scale the closure objective by two to keep every capacity integral.
    for omit in [None] + list(G):
        H = G.copy()
        if omit is not None:
            H.remove_node(omit)
        M = H.number_of_edges()
        Q = nx.DiGraph()
        source, sink = 'SOURCE', 'SINK'
        infinity = 2*M+11*len(H)+1
        for v in H:
            Q.add_edge(v, sink, capacity=11)
        for j, (u, v) in enumerate(H.edges()):
            node = ('edge', j)
            Q.add_edge(source, node, capacity=2)
            Q.add_edge(node, u, capacity=infinity)
            Q.add_edge(node, v, capacity=infinity)
        value, _ = nx.minimum_cut(Q, source, sink)
        assert 2*M-value == (1 if omit is None else 0)
        ST['independent exact maximum-closure tests'] += 1
    print('Even critical trap-repair example: k 12 n 83 e 457 d(s) 12 Delta(T) 4', flush=True)


def max_surplus(G, r, omit=None):
    H = G.copy()
    if omit is not None:
        H.remove_node(omit)
    D = nx.DiGraph()
    source, sink = "SOURCE", "SINK"
    M = H.number_of_edges()
    infinity = M+r*len(H)+1
    for v in H:
        D.add_edge(v, sink, capacity=r)
    for i, (u, v) in enumerate(H.edges()):
        node = ("edge", i)
        D.add_edge(source, node, capacity=1)
        D.add_edge(node, u, capacity=infinity)
        D.add_edge(node, v, capacity=infinity)
    value, _ = nx.minimum_cut(D, source, sink)
    return M-value


def critical_trap_audit():
    for ell in (3, 5, 7):
        G, r = critical_trap(ell)
        print("Critical trap-repair family:", "ell", ell, "k", 2*r+1,
              "n", len(G), "e", G.number_of_edges(), "d(s)", G.degree(0), flush=True)
        if ell == 3:
            assert max_surplus(G, r) == 1
            ST["independent exact maximum-closure tests"] += 1
            for v in G:
                assert max_surplus(G, r, v) == 0
                ST["independent exact maximum-closure tests"] += 1


def path_audit():
    """Small exact audit of endpoint inequality and marked path coverage."""
    for G0 in nx.graph_atlas_g():
        if not 1 <= len(G0) <= 6:
            continue
        G = nx.convert_node_labels_to_integers(G0)
        n = len(G)
        full = (1 << n)-1
        adj = [sum(1 << w for w in G[v]) for v in G]
        dp = [0]*(full+1)
        for v in G:
            dp[1 << v] = 1 << v
        for mask in range(1, full+1):
            for v in G:
                if dp[mask] >> v & 1:
                    for w in G[v]:
                        if not mask >> w & 1:
                            dp[mask | (1 << w)] |= 1 << w
        endpoints = dp[full]
        if endpoints:
            for v in G:
                if endpoints >> v & 1:
                    assert 2*adj[v].bit_count()-(adj[v] & endpoints).bit_count() <= n-1
                    ST['Hamiltonian endpoint potential checks'] += 1
        k = min(max(2*adj[v].bit_count()-(adj[v] & mask).bit_count()
                    for v in G if mask >> v & 1)
                for mask in range(1, full+1))
        if k >= 1:
            for v in G:
                longest = max(mask.bit_count()-1 for mask in range(1, full+1)
                              if dp[mask] and mask >> v & 1)
                assert longest >= k
                ST['W_k marked-vertex path coverage checks'] += 1


def main():
    assert hashlib.sha256((HERE/"Spec.lean").read_bytes()).hexdigest() == SPEC_SHA
    path_audit()
    multipartite_audit()
    clique_join_audit()
    bipartite_audit()
    spider_exception_audit()
    two_wing_audit()
    critical_trap_audit()
    even_critical_trap()
    for key, value in sorted(ST.items()):
        print(f"{key}: {value}")
    assert hashlib.sha256((HERE/"Spec.lean").read_bytes()).hexdigest() == SPEC_SHA
    print("PASS. General critical-host high-vertex coverage is NOT claimed.")


if __name__ == "__main__":
    main()
