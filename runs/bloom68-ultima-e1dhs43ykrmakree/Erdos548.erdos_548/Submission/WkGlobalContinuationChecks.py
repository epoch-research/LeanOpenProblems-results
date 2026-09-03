#!/usr/bin/env python3
"""Audits for WkGlobalContinuation.md.

These are checks of explicit proofs and constructions, NOT a search-based
proof of W_k or Erdos--Sos. Containment is non-induced throughout.
No existing file, in particular no Lean file, is written by this script.
"""
from __future__ import annotations

from collections import Counter
from hashlib import sha256
from itertools import combinations
from pathlib import Path

import networkx as nx

ST = Counter()
HERE = Path(__file__).resolve().parent
SPEC_SHA = "674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103"


def copy_ok(T, G, f):
    assert set(f) == set(T)
    assert len(set(f.values())) == len(T)
    assert set(f.values()) <= set(G)
    assert all(G.has_edge(f[u], f[v]) for u, v in T.edges())


def wk(G, k):
    rem = set(G)
    order = []
    while rem:
        v = next((v for v in rem
                  if 2 * G.degree(v) - len(set(G[v]) & rem) >= k), None)
        if v is None:
            return None
        rem.remove(v)
        order.append(v)
    return order


def weighted_wk(H, A, k):
    rem = set(H)
    order = []
    while rem:
        v = next((v for v in rem
                  if 2 * H.degree(v) - len(set(H[v]) & rem)
                  + 2 * int(v in A) >= k), None)
        if v is None:
            return None
        rem.remove(v)
        order.append(v)
    return order


def apex_identity_audit():
    for G in nx.graph_atlas_g():
        if not 2 <= len(G) <= 5:
            continue
        for k in range(1, len(G)):
            for s in G:
                if G.degree(s) < k:
                    continue
                H = G.subgraph(set(G) - {s}).copy()
                A = set(G[s])
                assert (wk(G, k) is not None) == (
                    weighted_wk(H, A, k) is not None)
                V = list(H)
                for mask in range(1, 1 << len(V)):
                    X = {V[i] for i in range(len(V)) if mask >> i & 1}
                    for v in X:
                        lhs = 2 * G.degree(v) - len(set(G[v]) & X)
                        rhs = (2 * H.degree(v) - len(set(H[v]) & X)
                               + 2 * int(v in A))
                        assert lhs == rhs
                        ST["exact weighted-apex potential identities"] += 1
                if wk(G, k) is not None and k >= 2:
                    assert wk(H, k - 2) is not None
                    ST["two-unit deletion audits"] += 1
                ST["weighted-apex equivalences"] += 1


def initialization_audit():
    # The initialization lemma assumes an available R-copy. Construct that
    # copy directly; no unproved lower-parameter embedding oracle is used.
    for n in range(4, 12):
        for T in nx.nonisomorphic_trees(n):
            k = n - 1
            if max(dict(T.degree()).values()) == k:
                continue
            leaves = {v for v in T if T.degree(v) == 1}
            core = T.subgraph(set(T) - leaves)
            for p in core:
                if core.degree(p) != 1:
                    continue
                q = next(iter(core[p]))
                L = set(T[p]) & leaves
                d = T.degree(p)
                assert len(L) == d - 1 >= 1
                R = T.subgraph(set(T) - L - {p}).copy()
                assert nx.is_tree(R) and q in R
                assert R.number_of_edges() == k - d <= k - 2
                rmap = {v: i for i, v in enumerate(sorted(R))}
                # H has k+1 vertices. Its only required edges are the R-copy.
                H = nx.empty_graph(k + 1)
                H.add_edges_from((rmap[u], rmap[v]) for u, v in R.edges())
                for root_allowed in (False, True):
                    A = (set(H) - {rmap[q]} if not root_allowed else set(H))
                    assert len(A) >= k
                    s = k + 1
                    G = H.copy()
                    G.add_node(s)
                    G.add_edges_from((s, x) for x in A)
                    f = dict(rmap)
                    f[p] = s
                    fresh = sorted(A - set(rmap.values()))
                    assert len(fresh) >= len(L)
                    f.update(zip(sorted(L), fresh))
                    assert set(f) == set(T) and len(set(f.values())) == n
                    bad = {frozenset((u, v)) for u, v in T.edges()
                           if not G.has_edge(f[u], f[v])}
                    assert bad == (set() if root_allowed
                                   else {frozenset((p, q))})
                    if root_allowed:
                        copy_ok(T, G, f)
                    ST["pendant-star one-defect initializations"] += 1


def subdivided_double_star(L):
    assert L >= 3 and L % 2 == 1
    T = nx.Graph()
    T.add_nodes_from(range(6))
    nxt = 6
    paths = {}
    for u, v in [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5)]:
        P = [u] + list(range(nxt, nxt + L - 1)) + [v]
        nxt += L - 1
        T.add_edges_from(zip(P, P[1:]))
        paths[u, v] = P
    assert nx.is_tree(T) and len(T) == 5 * L + 1
    assert max(dict(T.degree()).values()) == 3
    O = {v for v, d in nx.single_source_shortest_path_length(T, 0).items()
         if d % 2 == 0}
    D = set(T) - O
    a = (5 * L + 1) // 2
    assert len(O) == len(D) == a
    return T, paths, O, D


def host_adj(x, y, a):
    return (x < a) != (y < a)


def state_check(T, u, f, a, b, O):
    assert set(f) == set(T) - {u}
    assert len(set(f.values())) == len(f)
    assert all(1 <= x < a + b for x in f.values())  # omit fixed high s=0
    assert all(host_adj(f[x], f[y], a) for x, y in T.edges()
               if x != u and y != u)
    # Baseline is O -> host A', D -> host B. The allowed root set is B.
    flipped = {v for v in f if ((v in O) != (f[v] < a))}
    defect = sum(f[v] < a for v in T[u])
    return flipped, defect


def state_from_components(T, u, flip_vertices, a, b, O):
    HA = iter(range(1, a))
    HB = iter(range(a, a + b))
    f = {}
    for v in sorted(set(T) - {u}):
        into_A = (v in O) != (v in flip_vertices)
        f[v] = next(HA if into_A else HB)
    state_check(T, u, f, a, b, O)
    return f


def distance(T, u, f, v, g):
    # None is the hole symbol, counted as a label value.
    return sum(f.get(x) != g.get(x) for x in T)


def criticality_audit(a, b):
    r = a - 1
    n, e = a + b, a * b
    k = 2 * a - 1
    assert b == a * (a - 1) + 1
    assert n == a * a + 1 and e == r * n + 1
    assert b >= k and a == (k + 1) // 2
    # Each fixed-x surplus is affine in y. Endpoint checking therefore
    # certifies ALL proper induced-subset count types, not just a sample.
    for x in range(a + 1):
        ymax = b - 1 if x == a else b
        for y in {0, ymax}:
            assert x * y - r * (x + y) <= 0
            ST["criticality affine endpoint checks"] += 1
    # A first, B second is a W_k order.
    assert b >= k and 2 * a >= k
    ST["full-critical bipartite host certificates"] += 1


def deletion_deck_audit():
    for L in range(3, 34, 2):
        T, paths, O, D = subdivided_double_star(L)
        k = 5 * L
        a = (k + 1) // 2
        b = a * (a - 1) + 1
        criticality_audit(a, b)
        # Exhaust all color patterns of every punctured tree. Each feasible
        # pattern is realizable in the complete bipartite H=G-s.
        for u in T:
            comps = list(nx.connected_components(T.subgraph(set(T) - {u})))
            sizes = [len(C) for C in comps]
            assert sum(sizes) == k
            for mask in range(1 << len(comps)):
                F = set().union(*(comps[j] for j in range(len(comps))
                                  if mask >> j & 1))
                m = len(F)
                assert 0 <= m <= L or 2 * L <= m <= 3 * L or 4 * L <= m <= 5 * L
                ST["all-role punctured-tree color-band patterns"] += 1
                na = sum((v in O) != (v in F) for v in set(T) - {u})
                nb = k - na
                if na > a - 1 or nb > b:
                    continue
                f = state_from_components(T, u, F, a, b, O)
                flipped, defect = state_check(T, u, f, a, b, O)
                assert flipped == F
                if defect == 0:
                    assert m in (0, k)
                    full = dict(f)
                    full[u] = 0
                    assert len(set(full.values())) == k + 1
                    assert all(host_adj(full[x], full[y], a) for x, y in T.edges())
                    ST["explicit defect-zero full copies"] += 1
                ST["realized all-role forest color patterns"] += 1
        # Initial one-defect state: hole at c=0, flip just the middle component.
        c = 0
        middle = set(nx.node_connected_component(T.subgraph(set(T) - {c}), 1))
        assert len(middle) == 3 * L
        f = state_from_components(T, c, middle, a, b, O)
        flipped, defect = state_check(T, c, f, a, b, O)
        assert (len(flipped), defect) == (3 * L, 1)
        assert sum(x < a for x in f.values()) == a - 2
        assert sum(x >= a for x in f.values()) == a + 1
        ST["one-defect fixed-high trapped starting states"] += 1
        # Band gaps are exactly L, and flip-count variation <= label distance.
        assert 2 * L - L == 4 * L - 3 * L == L
        # Explicit sharp-size global move: flip one entire pendant arm.
        arm = set(paths[0, 2][1:])
        assert len(arm) == L and not (arm & flipped)
        old = dict(f)
        oldA = sorted(f[x] for x in arm if f[x] < a)
        oldB = sorted(f[x] for x in arm if f[x] >= a)
        freeA = next(x for x in range(1, a) if x not in set(f.values()))
        newA = iter(oldA + [freeA])
        newB = iter(oldB[:-1])
        for x in sorted(arm):
            f[x] = next(newB if x in O else newA)
        assert distance(T, c, old, c, f) == L
        flipped, defect = state_check(T, c, f, a, b, O)
        assert (len(flipped), defect) == (4 * L, 2)
        ST["verified linear-size whole-component flips"] += 1
        # Move the hole down the remaining baseline pendant path.
        u = c
        for v in paths[0, 3][1:]:
            assert all(host_adj(f[v], f[w], a) for w in T[u] if w != v)
            old, old_u = dict(f), u
            f[u] = f[v]
            del f[v]
            u = v
            assert distance(T, old_u, old, u, f) == 2
            flipped, defect = state_check(T, u, f, a, b, O)
            ST["verified hole pivots after the global flip"] += 1
        assert u in D
        assert (len(flipped), defect) == (k, 0)
        f[u] = 0
        assert set(f) == set(T) and len(set(f.values())) == k + 1
        assert set(range(a)) <= set(f.values())
        assert all(host_adj(f[x], f[y], a) for x, y in T.edges())
        ST["constructive covering repairs, all high vertices covered"] += 1


def blocker_instances(T, G):
    assert not nx.algorithms.isomorphism.GraphMatcher(G, T).subgraph_is_monomorphic()
    k = T.number_of_edges()
    Delta = max(dict(T.degree()).values())
    for ell in T:
        if T.degree(ell) != 1:
            continue
        p = next(iter(T[ell]))
        U = T.subgraph(set(T) - {ell}).copy()
        gm = nx.algorithms.isomorphism.GraphMatcher(G, U)
        for inv in gm.subgraph_monomorphisms_iter():
            f = {v: x for x, v in inv.items()}
            S = set(f.values())
            P = {v for v in U if G.has_edge(f[p], f[v])}
            assert set(G[f[p]]) <= S
            assert len(P) == G.degree(f[p]) and p not in P
            for z in set(G) - S:
                B = {v for v in U if not G.has_edge(z, f[v])}
                assert p in B
                NB = set().union(*(set(U[v]) for v in B))
                assert P <= NB
                assert (G.degree(f[p]) <= len(NB)
                        <= sum(U.degree(v) for v in B)
                        == sum(T.degree(v) for v in B) - 1
                        <= Delta * len(B) - 1)
                ST["exact target-sensitive leaf-blocker inequalities"] += 1


def blocker_audit():
    trees = {n: list(nx.nonisomorphic_trees(n)) for n in range(3, 7)}
    for G in nx.graph_atlas_g():
        if not 3 <= len(G) <= 5:
            continue
        for n in range(3, len(G) + 1):
            for T in trees[n]:
                if nx.algorithms.isomorphism.GraphMatcher(G, T).subgraph_is_monomorphic():
                    continue
                blocker_instances(T, G)
    # A minimum-degree-three, tree-free spider trap with real leaf-deleted copies.
    T = nx.Graph([(0, 1), (1, 2), (0, 3), (3, 4), (0, 5), (5, 6)])
    G = nx.Graph()
    G.add_edges_from(combinations(range(1, 4), 2))
    G.add_edges_from(combinations(range(4, 7), 2))
    G.add_edges_from((0, v) for v in range(1, 7))
    assert min(dict(G.degree()).values()) == 3
    blocker_instances(T, G)


def first_trigger_counter_audit():
    T = nx.balanced_tree(3, 4)
    assert len(T) == 121 and T.number_of_edges() == 120
    assert max(dict(T.degree()).values()) == 4
    for U in combinations(T, 2):
        sizes = [len(C) for C in nx.connected_components(T.subgraph(set(T) - set(U)))]
        sums = {0}
        for c in sizes:
            sums |= {s + c for s in sums}
        assert 59 not in sums
        ST["ternary-tree two-vertex separator capacity audits"] += 1
    A, B = set(range(59)), set(range(59, 119))
    s, t = 119, 120
    G = nx.Graph()
    G.add_edges_from(combinations(A, 2))
    G.add_edges_from(combinations(B, 2))
    G.add_edges_from((v, x) for v in (s, t) for x in A | B)
    G.add_edge(s, t)
    G.remove_edge(t, 59)
    assert len(G) == 121 and G.number_of_edges() == 3719
    assert min(dict(G.degree()).values()) == 60
    assert G.degree(s) == 120 and G.degree(t) == 119
    high = {v for v in G if G.degree(v) >= 120}
    assert high == {s}
    assert G.degree(t) + len(set(G[t]) & high) == 120
    assert all(2 * G.degree(v) - len(set(G[v]) & A) == 62 for v in A)
    assert wk(G, 120) is None
    ST["explicit first-trigger counterexample certificates"] += 1


def main():
    assert sha256((HERE / "Spec.lean").read_bytes()).hexdigest() == SPEC_SHA
    apex_identity_audit()
    initialization_audit()
    deletion_deck_audit()
    blocker_audit()
    first_trigger_counter_audit()
    for name, count in sorted(ST.items()):
        print(f"{name}: {count}")
    print("PASS: explicit proofs/constructions audited; unrestricted W_k remains unresolved.")
    assert sha256((HERE / "Spec.lean").read_bytes()).hexdigest() == SPEC_SHA


if __name__ == "__main__":
    main()
