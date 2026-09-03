#!/usr/bin/env python3
"""Exact checks for ResearchTreeHitting.md; never modifies an existing file.

Default: all graph-atlas connected even graphs / all trees through order 7,
all small rooted SP states, the sharp forest obstruction, and global double-
star constructions.  --exhaustive-through 9 additionally uses nauty-geng and
nauty-pickg and a complete cycle-avoidance branching proof for orders 8 and 9.
The latter is exhaustive over trees, NOT a random sample.  It can take tens
of minutes.  All partition decisions and certificates use integer arithmetic.

Dependencies: Python 3, networkx, and the existing ResearchRoundingCheck.py
(which itself imports numpy/scipy).  No numerical optimizer is used here.
"""
import argparse
from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import random
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True
import networkx as nx
from ResearchRoundingCheck import all_cycles, cycle_edges, path_edges

SPEC_SHA256 = "429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde"


def edge(u, v):
    assert u != v
    return tuple(sorted((u, v)))


def edges(G):
    return frozenset(edge(u, v) for u, v in G.edges())


def even(G):
    return all(d % 2 == 0 for _, d in G.degree())


def verify_partition(G, cycles, paths=(), marked=None, terminals=None):
    used = Counter()
    for C in cycles:
        ee = cycle_edges(C)
        assert ee <= edges(G)
        if marked is not None:
            assert ee & marked
        used.update(ee)
    for P in paths:
        assert len(P) >= 2 and len(P) == len(set(P))
        if terminals is not None:
            assert (P[0], P[-1]) == terminals
        used.update(path_edges(P))
    assert used == Counter({e: 1 for e in edges(G)})


def forest_masks(G, components=1):
    """Every labelled spanning forest with the specified component count."""
    es = sorted(edges(G))
    vs = sorted(G)
    vi = {v: i for i, v in enumerate(vs)}
    n = len(vs)
    if not 1 <= components <= n:
        return
    for inds in combinations(range(len(es)), n-components):
        parent = list(range(n))

        def root(v):
            while parent[v] != v:
                v = parent[v]
            return v

        for i in inds:
            a, b = (root(vi[v]) for v in es[i])
            if a == b:
                break
            parent[a] = b
        else:
            yield sum(1 << i for i in inds)


class CycleInstance:
    """All simple cycles + integer edge-mask exact cover; no tolerances."""
    def __init__(self, G):
        self.G = G.copy()
        self.es = sorted(edges(G))
        self.ix = {e: i for i, e in enumerate(self.es)}
        self.cycles = sorted(all_cycles(G), key=lambda C: -len(C))
        self.masks = [self.mask(cycle_edges(C)) for C in self.cycles]
        self.by_edge = [[] for _ in self.es]
        for j, m in enumerate(self.masks):
            b = m
            while b:
                bit = b & -b
                b -= bit
                self.by_edge[bit.bit_length()-1].append(j)
        self.full = (1 << len(self.es))-1

    def mask(self, ee):
        return sum(1 << self.ix[e] for e in ee)

    def edge_set(self, mask):
        return frozenset(e for i, e in enumerate(self.es) if mask >> i & 1)

    def partition(self, red):
        allowed = [bool(m & red) for m in self.masks]
        by = [[j for j in js if allowed[j]] for js in self.by_edge]

        @lru_cache(None)
        def solve(rem):
            if not rem:
                return ()
            best = None
            left = rem
            while left:
                bit = left & -left
                left -= bit
                opts = [j for j in by[bit.bit_length()-1]
                        if self.masks[j] & rem == self.masks[j]]
                if not opts:
                    return None
                if best is None or len(opts) < len(best):
                    best = opts
                    if len(best) == 1:
                        break
            for j in best:
                rest = solve(rem ^ self.masks[j])
                if rest is not None:
                    return (j,) + rest
            return None

        D = solve(self.full)
        if D is not None:
            # Independently check the returned cover before using it as a
            # universal-branching certificate.
            used = 0
            for j in D:
                assert self.masks[j] & red
                assert not used & self.masks[j]
                used |= self.masks[j]
            assert used == self.full
        return D

    def universal_trees(self):
        """Complete recursion over all possible bad trees, not tree sampling.

        At state A every candidate tree is contained in A.  Choose one such
        tree and obtain a partition D hitting it.  A counterexample tree must
        miss some C in D, hence is contained in A\E(C).  These children cover
        ALL counterexample candidates.  Disconnected children contain none.
        """
        vs = sorted(self.G)
        vi = {v: i for i, v in enumerate(vs)}
        adj = [[] for _ in vs]
        for i, (a, b) in enumerate(self.es):
            adj[vi[a]].append((vi[b], 1 << i))
            adj[vi[b]].append((vi[a], 1 << i))

        def find_tree(avail):
            used, stack, red = 1, [0], 0
            while stack:
                a = stack.pop()
                for b, bit in adj[a]:
                    if bit & avail and not (used >> b & 1):
                        used |= 1 << b
                        stack.append(b)
                        red |= bit
            return red if used == (1 << len(vs))-1 else None

        seen = set()
        max_depth = 0

        def visit(avail, depth):
            nonlocal max_depth
            if avail in seen:
                return None
            seen.add(avail)
            max_depth = max(max_depth, depth)
            red = find_tree(avail)
            if red is None:
                return None
            D = self.partition(red)
            if D is None:
                return red
            for j in D:
                child = avail & ~self.masks[j]
                assert child != avail
                if child.bit_count() < len(vs)-1:
                    continue
                if find_tree(child) is None:
                    continue
                fail = visit(child, depth+1)
                if fail is not None:
                    return fail
            return None

        fail = visit(self.full, 0)
        return fail, {"states": len(seen), "max_depth": max_depth}


def tree_count(G):
    """Matrix-tree theorem with exact fraction-free Bareiss elimination."""
    vs = sorted(G)
    if len(vs) == 1:
        return 1
    A = [[G.degree(u) if u == v else -int(G.has_edge(u, v))
          for v in vs[:-1]] for u in vs[:-1]]
    prev, sign, n = 1, 1, len(A)
    for k in range(n-1):
        if A[k][k] == 0:
            j = next(j for j in range(k+1, n) if A[j][k])
            A[k], A[j] = A[j], A[k]
            sign *= -1
        pivot = A[k][k]
        for i in range(k+1, n):
            for j in range(k+1, n):
                num = A[i][j]*pivot-A[i][k]*A[k][j]
                assert num % prev == 0
                A[i][j] = num//prev
        for i in range(k+1, n):
            A[i][k] = 0
        prev = pivot
    return sign*A[-1][-1]


# -------- The marked two-terminal series-parallel construction --------

@dataclass(frozen=True)
class Network:
    kind: str
    s: int
    t: int
    ee: frozenset
    vv: frozenset
    capacity: int
    parity: int
    left: object = None
    right: object = None


def leaf(s, t):
    return Network("E", s, t, frozenset({edge(s, t)}),
                   frozenset({s, t}), 1, 1)


def series(A, B):
    assert A.t == B.s and A.vv & B.vv == {A.t}
    assert A.parity == B.parity, "The internal junction must have even degree."
    assert not A.ee & B.ee
    return Network("S", A.s, B.t, A.ee | B.ee, A.vv | B.vv,
                   min(A.capacity, B.capacity), A.parity, A, B)


def parallel(A, B):
    assert (A.s, A.t) == (B.s, B.t)
    assert A.vv & B.vv == {A.s, A.t} and not A.ee & B.ee
    return Network("P", A.s, A.t, A.ee | B.ee, A.vv | B.vv,
                   A.capacity+B.capacity, (A.parity+B.parity) % 2, A, B)


def reverse(N):
    if N.kind == "E":
        return leaf(N.t, N.s)
    if N.kind == "S":
        return series(reverse(N.right), reverse(N.left))
    return parallel(reverse(N.left), reverse(N.right))


def orient(N, s, t):
    if (N.s, N.t) == (s, t):
        return N
    assert (N.s, N.t) == (t, s)
    return reverse(N)


def as_graph(N):
    G = nx.Graph()
    G.add_nodes_from(N.vv)
    G.add_edges_from(N.ee)
    return G


def recognize_network(G, s, t):
    """Exact series / parallel reduction, retaining original edge sets."""
    if not nx.is_connected(G) or any(G.degree(v) % 2 for v in G if v not in (s, t)):
        return None
    Q = nx.MultiGraph()
    Q.add_nodes_from(G)
    for u, v in G.edges():
        Q.add_edge(u, v, node=leaf(u, v))
    while True:
        changed = False
        for u, v in sorted({edge(a, b) for a, b in Q.edges()}):
            ks = list(Q[u][v])
            if len(ks) >= 2:
                A = orient(Q[u][v][ks[0]]["node"], u, v)
                B = orient(Q[u][v][ks[1]]["node"], u, v)
                Q.remove_edge(u, v, ks[0])
                Q.remove_edge(u, v, ks[1])
                Q.add_edge(u, v, node=parallel(A, B))
                changed = True
                break
        if changed:
            continue
        for w in sorted(Q):
            if w in (s, t) or Q.degree(w) != 2:
                continue
            inc = list(Q.edges(w, keys=True, data=True))
            u, v = inc[0][1], inc[1][1]
            if u == v:
                continue
            A = orient(inc[0][3]["node"], u, w)
            B = orient(inc[1][3]["node"], w, v)
            if A.parity != B.parity:
                return None
            C = series(A, B)
            Q.remove_node(w)
            Q.add_edge(u, v, node=C)
            changed = True
            break
        if not changed:
            break
    if set(Q) != {s, t} or Q.number_of_edges() != 1 or not Q.has_edge(s, t):
        return None
    N = orient(next(iter(Q[s][t].values()))["node"], s, t)
    assert N.ee == edges(G) and N.vv == set(G)
    return N


def rooted_forest_state(N, red):
    R = nx.Graph()
    R.add_nodes_from(N.vv)
    R.add_edges_from(N.ee & red)
    assert nx.is_forest(R)
    cc = list(nx.connected_components(R))
    assert len(cc) in (1, 2)
    assert all(C & {N.s, N.t} for C in cc)
    return len(cc)


def join_cycle(P, Q):
    assert (P[0], P[-1]) == (Q[0], Q[-1])
    assert set(P[1:-1]).isdisjoint(Q[1:-1])
    C = tuple(P) + tuple(Q[-2:0:-1])
    assert len(C) >= 3 and len(C) == len(set(C))
    return C


def sp_decompose(N, p, red):
    """Return p s--t paths and cycles; only the blue edge st may be a bad path.

    If p=1 and the marked forest is connected, even that exception is absent.
    Every cycle meets red.  This is the proved recurrence, not exact-cover
    search over the desired output.
    """
    assert 0 <= p <= N.capacity and p % 2 == N.parity
    state = rooted_forest_state(N, red)
    direct = edge(N.s, N.t)
    if N.kind == "E":
        assert p == 1
        return [(N.s, N.t)], []

    # The one-export-path invariant used at series junctions.  Delete the
    # unique blue terminal edge; the remaining connected even network has
    # at least two edge-disjoint terminal paths, both marked by induction.
    if N.kind == "P" and p == 1 and state == 1 and direct in N.ee-red:
        B = as_graph(N)
        B.remove_edge(*direct)
        K = recognize_network(B, N.s, N.t)
        assert K is not None and K.parity == 0 and K.capacity >= 2
        P, D = sp_decompose(K, 2, red)
        assert all(path_edges(Q) & red for Q in P)
        return [P[1]], D + [join_cycle((N.s, N.t), P[0])]

    if N.kind == "S":
        P, D = sp_decompose(N.left, p, red)
        Q, E = sp_decompose(N.right, p, red)
        bad_P = [i for i, X in enumerate(P) if not path_edges(X) & red]
        bad_Q = [i for i, X in enumerate(Q) if not path_edges(X) & red]
        assert len(bad_P) <= 1 and len(bad_Q) <= 1
        if bad_P and bad_Q:
            assert p >= 2
            if bad_P[0] == bad_Q[0]:
                j, k = bad_Q[0], (bad_Q[0]+1) % p
                Q[j], Q[k] = Q[k], Q[j]
        paths = [tuple(a)+tuple(b[1:]) for a, b in zip(P, Q)]
        assert all(path_edges(X) & red for X in paths)
        return paths, D+E

    a = min(N.left.capacity, p+N.right.capacity)
    b = min(N.right.capacity, p+N.left.capacity)
    assert (a+b-p) % 2 == 0
    h = (a+b-p)//2
    assert 0 <= h <= min(a, b)
    P, D = sp_decompose(N.left, a, red)
    Q, E = sp_decompose(N.right, b, red)
    assert sum(not path_edges(X) & red for X in P+Q) <= 1
    cycles = [join_cycle(x, y) for x, y in zip(P[:h], Q[:h])]
    return P[h:]+Q[h:], D+E+cycles


def is_even_sp(G):
    if not even(G) or not nx.is_connected(G):
        return False
    for ee in nx.biconnected_component_edges(G):
        B = nx.Graph(list(ee))
        s, t = next(iter(B.edges()))
        if recognize_network(B, s, t) is None:
            return False
    return True


def sp_graph_partition(G, red):
    """Global construction for an even SP graph and a <=2-component forest."""
    assert even(G) and nx.is_connected(G)
    R = nx.Graph()
    R.add_nodes_from(G)
    R.add_edges_from(red)
    assert red <= edges(G) and nx.is_forest(R)
    assert nx.number_connected_components(R) <= 2
    answer = []
    for ee in nx.biconnected_component_edges(G):
        B = nx.Graph(list(ee))
        assert even(B)
        RB = nx.Graph()
        RB.add_nodes_from(B)
        RB.add_edges_from(red & edges(B))
        cc = list(nx.connected_components(RB))
        assert len(cc) in (1, 2)
        if len(cc) == 2:
            s, t = next((u, v) for u, v in B.edges() if (u in cc[0]) != (v in cc[0]))
        else:
            s, t = next(iter(B.edges()))
        N = recognize_network(B, s, t)
        assert N is not None
        P, D = sp_decompose(N, 0, red)
        assert not P
        answer += D
    verify_partition(G, answer, marked=red)
    assert len(answer) <= len(red)
    return answer


def check_sp_construction():
    graph_count, forest_cases = 0, 0
    for G in nx.graph_atlas_g():
        if not G or not is_even_sp(G):
            continue
        graph_count += 1
        es = sorted(edges(G))
        for c in (1, 2):
            for m in forest_masks(G, c):
                red = frozenset(e for i, e in enumerate(es) if m >> i & 1)
                sp_graph_partition(G, red)
                forest_cases += 1

    # Test the full path invariant, including odd terminal degree and the
    # p=1 exceptional branch, not only the final p=0 statement.
    networks, states = 0, 0
    for G in nx.graph_atlas_g():
        if not 2 <= len(G) <= 6 or not nx.is_connected(G):
            continue
        odd = {v for v, d in G.degree() if d % 2}
        if len(odd) > 2:
            continue
        pairs = [tuple(sorted(odd))] if odd else list(combinations(sorted(G), 2))
        es = sorted(edges(G))
        forests = [(c, frozenset(e for i, e in enumerate(es) if m >> i & 1))
                   for c in (1, 2) for m in forest_masks(G, c)]
        for s, t in pairs:
            N = recognize_network(G, s, t)
            if N is None:
                continue
            networks += 1
            for c, red in forests:
                R = nx.Graph()
                R.add_nodes_from(G)
                R.add_edges_from(red)
                if c == 2 and nx.has_path(R, s, t):
                    continue
                for p in range(N.parity, N.capacity+1, 2):
                    P, D = sp_decompose(N, p, red)
                    verify_partition(G, D, P, red, (s, t))
                    assert len(P) == p
                    bad = [Q for Q in P if not path_edges(Q) & red]
                    assert len(bad) <= 1
                    assert all(Q == (s, t) and edge(s, t) not in red for Q in bad)
                    if p == 1 and c == 1:
                        assert not bad
                    states += 1
    return {"even_SP_atlas_graphs": graph_count,
            "all_tree_and_two_forest_cases": forest_cases,
            "rooted_networks_through_6": networks,
            "all_rooted_forest_p_states": states}


# -------- Sharp boundary and a non-SP global family --------

def check_three_forest_obstruction():
    branches = [(0, 2, 3, 1), (0, 1), (0, 4, 1), (0, 5, 1)]
    G = nx.Graph(e for P in branches for e in zip(P, P[1:]))
    red = path_edges(branches[0])
    R = nx.Graph()
    R.add_nodes_from(G)
    R.add_edges_from(red)
    assert even(G) and nx.is_biconnected(G) and is_even_sp(G)
    assert nx.is_forest(R) and nx.number_connected_components(R) == 3
    I = CycleInstance(G)
    assert len(I.cycles) == 6
    assert I.partition(I.mask(red)) is None
    # Farkas certificate: all allowed cycles have price 0, total price is 2.
    y = {e: 0 for e in edges(G)}
    y[edge(0, 2)] = -1
    for P in branches[1:]:
        y[edge(P[0], P[1])] = 1
    allowed = [C for C in I.cycles if cycle_edges(C) & red]
    assert len(allowed) == 3
    assert all(sum(y[e] for e in cycle_edges(C)) == 0 for C in allowed)
    assert sum(y.values()) == 2
    D = [join_cycle(branches[0], branches[1]),
         join_cycle(branches[2], branches[3])]
    verify_partition(G, D)
    # Adding one edge gives a two-component forest, not a feedback set:
    # a blue cycle still exists, but the SP construction succeeds.
    red2 = red | {edge(0, 4)}
    assert any(not cycle_edges(C) & red2 for C in I.cycles)
    sp_graph_partition(G, red2)
    return {"n": len(G), "m": G.number_of_edges(), "cycles": 6,
            "allowed_cycles": 3, "unrestricted_c_and_cf": 2,
            "Farkas_total": 2, "counterexample_is_to_three_forest_only": True}


def cubic_double_star(H, A):
    A, B = set(A), set(H)-set(A)
    k = len(A)
    assert len(B) == k and k >= 9 and k % 2 == 1
    assert all(d == 3 for _, d in H.degree())
    assert all((u in A) != (v in A) for u, v in H.edges())
    M = nx.algorithms.bipartite.maximum_matching(H, top_nodes=A)
    assert len(M) == len(H)
    matched = [edge(u, M[u]) for u in sorted(A)]
    J = H.copy()
    J.remove_edges_from(matched)
    assert all(d == 2 for _, d in J.degree())
    sigma = {}
    for cc in nx.connected_components(J):
        C = [min(cc)]
        prev, cur = None, C[0]
        while True:
            nxt = next(v for v in sorted(J[cur]) if v != prev)
            if nxt == C[0]:
                break
            C.append(nxt)
            prev, cur = cur, nxt
        assert set(C) == cc
        sigma.update(zip(C, C[1:]+C[:1]))
    P = []
    for u, v in matched:
        Q = (sigma[u], u, v, sigma[v])
        if Q[0] not in A:
            Q = Q[::-1]
        P.append(Q)
    verify_partition(H, [], P)
    assert Counter(v for Q in P for v in (Q[0], Q[-1])) == Counter({v: 1 for v in H})
    assert Counter(v for Q in P for v in Q) == Counter({v: 2 for v in H})
    K = nx.Graph()
    K.add_nodes_from(range(k))
    K.add_edges_from((i, j) for i, j in combinations(range(k), 2)
                     if set(P[i]).isdisjoint(P[j]))
    assert min(d for _, d in K.degree()) >= k-5 >= (k-1)//2
    pairing = nx.max_weight_matching(K, maxcardinality=True)
    assert len(pairing) == (k-1)//2
    used = {v for e in pairing for v in e}
    single, = set(range(k))-used
    s, t = max(H)+1, max(H)+2
    G = H.copy()
    red = frozenset([edge(s, v) for v in A] + [edge(t, v) for v in B] + [edge(s, t)])
    G.add_edges_from(red)
    T = nx.Graph()
    T.add_nodes_from(G)
    T.add_edges_from(red)
    assert nx.is_tree(T) and even(G)
    D = [(s,) + P[single] + (t,)]
    for i, j in sorted(tuple(sorted(e)) for e in pairing):
        D.append((s,) + P[i] + (t,) + P[j][::-1])
    verify_partition(G, D, marked=red)
    assert len(D) == (k+1)//2 == G.degree(s)//2
    assert sorted(map(len, D)) == [6] + [10]*((k-1)//2)
    return G, red, D


def check_double_stars():
    rng = random.Random(744901)
    cases, largest = 0, 0
    for k in [9, 11, 13, 15, 21, 31, 51, 101]:
        for trial in range(4):
            H = nx.Graph((i, k+(i+d) % k) for i in range(k) for d in (-1, 0, 1))
            # Bipartite two-edge switches give further cubic inputs.
            for _ in range(trial*20*k):
                a, b = rng.sample(range(k), 2)
                x, y = rng.choice(list(H[a])), rng.choice(list(H[b]))
                if x != y and not H.has_edge(a, y) and not H.has_edge(b, x):
                    H.remove_edges_from([(a, x), (b, y)])
                    H.add_edges_from([(a, y), (b, x)])
            G, _, _ = cubic_double_star(H, range(k))
            largest = max(largest, len(G))
            cases += 1
    H = nx.disjoint_union_all([nx.complete_bipartite_graph(3, 3) for _ in range(3)])
    A = {6*j+i for j in range(3) for i in range(3)}
    cubic_double_star(H, A)
    return {"families_checked": cases+1, "largest_n": largest,
            "global_c_and_cf": "(k+1)/2 = n/4", "cycle_lengths": [6, 10]}


def check_hamilton_subdivision():
    cases, cycle_maps = 0, 0
    for G in nx.graph_atlas_g():
        if not 3 <= len(G) <= 6 or not nx.is_connected(G) or not even(G):
            continue
        cs = list(all_cycles(G))
        for F in cs:
            if len(F) != len(G):
                continue
            u, v, w = F[0], F[1], len(G)
            e = edge(u, v)
            H = G.copy()
            H.remove_edge(u, v)
            H.add_edges_from([(u, w), (w, v)])
            red = (cycle_edges(F)-{e}) | {edge(u, w)}
            T = nx.Graph()
            T.add_nodes_from(H)
            T.add_edges_from(red)
            assert nx.is_tree(T) and max(dict(T.degree()).values()) == 2 and even(H)
            lifted = set()
            for C in cs:
                Q = []
                for a, b in zip(C, C[1:]+C[:1]):
                    Q.append(a)
                    if edge(a, b) == e:
                        Q.append(w)
                qe = cycle_edges(tuple(Q))
                assert bool(qe & red) == bool(cycle_edges(C) & cycle_edges(F))
                lifted.add(qe)
                cycle_maps += 1
            assert lifted == {cycle_edges(C) for C in all_cycles(H)}
            cases += 1
    return {"Hamilton_inputs_through_6": cases, "exact_cycle_bijections": cycle_maps}


# -------- Bounded exhaustive diagnostics --------

def scan_atlas():
    counts = {}
    for G in nx.graph_atlas_g():
        if not G or not nx.is_connected(G) or not even(G):
            continue
        n = len(G)
        row = counts.setdefault(n, {"graphs": 0, "trees": 0, "Hamilton_cycles": 0})
        row["graphs"] += 1
        I = CycleInstance(G)
        local_trees = 0
        for red in forest_masks(G):
            D = I.partition(red)
            assert D is not None, (n, I.es, sorted(I.edge_set(red)))
            verify_partition(G, [I.cycles[j] for j in D], marked=I.edge_set(red))
            local_trees += 1
        assert local_trees == tree_count(G)
        row["trees"] += local_trees
        for C, red in zip(I.cycles, I.masks):
            if len(C) == n:
                assert I.partition(red) is not None
                row["Hamilton_cycles"] += 1
    return counts


def nauty_even_graphs(n):
    geng = shutil.which("nauty-geng") or shutil.which("geng")
    pickg = shutil.which("nauty-pickg") or shutil.which("pickg")
    assert geng and pickg, "Install nauty for the optional exhaustive extension."
    p = subprocess.Popen([geng, "-cq", str(n)], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    q = subprocess.Popen([pickg, "-q", "-E"], stdin=p.stdout,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    p.stdout.close()
    for line in q.stdout:
        G = nx.from_graph6_bytes(line.strip())
        assert nx.is_connected(G) and even(G)
        yield line, G
    assert q.wait() == 0, q.stderr.read().decode()
    assert p.wait() == 0, p.stderr.read().decode()


def scan_extended(n):
    result = {"graphs": 0, "trees": 0, "Hamilton_cycles": 0,
              "coverage_states": 0, "largest_coverage_search": 0}
    digest = sha256()
    started = time.time()
    for line, G in nauty_even_graphs(n):
        digest.update(line)
        I = CycleInstance(G)
        fail, stats = I.universal_trees()
        assert fail is None, {"n": n, "graph6": line.decode().strip(),
                              "edges": I.es, "tree": sorted(I.edge_set(fail))}
        result["graphs"] += 1
        result["trees"] += tree_count(G)
        result["Hamilton_cycles"] += sum(len(C) == n for C in I.cycles)
        result["coverage_states"] += stats["states"]
        result["largest_coverage_search"] = max(result["largest_coverage_search"], stats["states"])
        if result["graphs"] % 100 == 0:
            print(json.dumps({"progress_n": n, **result,
                              "seconds": round(time.time()-started, 2)}), flush=True)
    result["graph6_sha256"] = digest.hexdigest()
    # Every Hamilton cycle contains a spanning tree.  Thus the all-tree
    # certificate also verifies every specified Hamilton cycle in this row.
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exhaustive-through", type=int, choices=(7, 8, 9), default=7)
    parser.add_argument("--proof-checks-only", action="store_true")
    args = parser.parse_args()
    spec = Path(__file__).with_name("Spec.lean")
    before = sha256(spec.read_bytes()).hexdigest()
    assert before == SPEC_SHA256
    started = time.time()
    result = {"SP_construction": check_sp_construction(),
              "sharp_forest_obstruction": check_three_forest_obstruction(),
              "double_star_construction": check_double_stars(),
              "Hamilton_subdivision": check_hamilton_subdivision()}
    print(json.dumps({"proof_checks": result}, sort_keys=True), flush=True)
    if not args.proof_checks_only:
        result["atlas_all_trees_and_Hamilton_cycles"] = scan_atlas()
        for n in range(8, args.exhaustive_through+1):
            result[f"order_{n}_all_trees"] = scan_extended(n)
    assert sha256(spec.read_bytes()).hexdigest() == before
    result["Spec_unchanged_sha256"] = before
    result["seconds"] = round(time.time()-started, 2)
    print(json.dumps(result, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
