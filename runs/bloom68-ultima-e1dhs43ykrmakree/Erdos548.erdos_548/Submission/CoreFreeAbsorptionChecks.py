#!/usr/bin/env python3
"""Core-first cut audit and independently verified terminal certificates.

Uses AbsorptionCutChecks.py without changing it.  Every graph passed to its
bitmask routines is normalized to numeric vertex iteration order.  The finite
coverage assertions concern exactly the ranges printed by this script.
No Lean file, specification, or other agent's output is written.
"""
from __future__ import annotations

from collections import Counter
from functools import lru_cache
from itertools import combinations, product
import argparse
import shutil
import subprocess
import time

import networkx as nx

import AbsorptionCutChecks as old

COUNTS = Counter()


def ordered(G):
    assert set(G) == set(range(len(G)))
    J = nx.Graph()
    J.add_nodes_from(range(len(G)))
    J.add_edges_from(G.edges())
    assert list(J) == list(range(len(J)))
    return J


def masks(G):
    return [sum(1 << w for w in G[v]) for v in range(len(G))]


def verify_copy(T, G, phi):
    assert set(phi) == set(T)
    assert len(set(phi.values())) == len(T)
    assert set(phi.values()) <= set(G)
    assert all(G.has_edge(phi[u], phi[v]) for u, v in T.edges())
    COUNTS['constructive copies verified'] += 1


def grow(T, Q, phi):
    """Extend a connected partial tree, keeping its already assigned images."""
    phi = dict(phi)
    while len(phi) < len(T):
        p, x = next((p, x) for p in phi for x in T[p] if x not in phi)
        unused = set(Q[phi[p]]) - set(phi.values())
        assert unused
        phi[x] = min(unused)
    return phi


def core_terminal_copy(T, G):
    k = T.number_of_edges()
    assert nx.is_tree(T) and nx.is_connected(G)
    star = next((v for v in T if T.degree(v) == k), None)
    if star is not None:
        s = next(v for v in G if G.degree(v) >= k)
        phi = {star: s}
        phi.update(zip((v for v in T if v != star), sorted(G[s])))
    else:
        K = nx.k_core(G, k - 1)
        assert K
        C = next(iter(nx.connected_components(K)))
        Q = G.subgraph(C)
        assert min(dict(Q.degree()).values()) >= k - 1
        assert len(Q) >= k
        if len(Q) == k:
            assert Q.number_of_edges() == k * (k - 1) // 2
            v, outside = next((v, w) for v in Q for w in G[v] if w not in Q)
            ell = next(v for v in T if T.degree(v) == 1)
            p = next(iter(T[ell]))
            phi = {ell: outside, p: v}
            phi.update(zip((x for x in T if x not in phi), sorted(set(Q) - {v})))
        elif Q.number_of_edges() == len(Q) * (len(Q) - 1) // 2:
            phi = dict(zip(T, sorted(Q)))
        else:
            v0, z0 = next((v, z) for v, z in combinations(Q, 2) if not Q.has_edge(v, z))
            v, w, z = nx.shortest_path(Q, v0, z0)[:3]
            assert not Q.has_edge(v, z)
            start = next(iter(T))
            ell = max(nx.single_source_shortest_path_length(T, start),
                      key=nx.single_source_shortest_path_length(T, start).get)
            paths = nx.single_source_shortest_path(T, ell)
            diameter = max(paths.values(), key=len)
            ell, p, q, rr = diameter[:4]
            assert T.degree(ell) == 1
            S = T.copy()
            S.remove_node(ell)
            phi = grow(S, Q, {p: v, q: w, rr: z})
            assert not Q.has_edge(phi[p], phi[rr])
            fresh = set(Q[v]) - set(phi.values())
            assert fresh
            phi[ell] = min(fresh)
    verify_copy(T, G, phi)
    return phi


def audit_core_terminal():
    # Old regular-core examples are terminal FIRST, even when their cut test fails.
    for flavor in ('rook', 'cliques'):
        for r in range(3, 13):
            G, *_ = old.regular_core_host(r, flavor)
            G = ordered(G)
            k = 2 * r + 1
            assert nx.k_core(G, k - 1)
            COUNTS['old regular-core hosts correctly terminal'] += 1
            if r <= 4:
                for T in nx.nonisomorphic_trees(k + 1):
                    core_terminal_copy(ordered(T), G)
    # Also audit the K_k plus boundary case, without depending on the old family.
    for k in range(3, 9):
        G = nx.complete_graph(k)
        G.add_edge(0, k)
        for T in nx.nonisomorphic_trees(k + 1):
            core_terminal_copy(ordered(T), ordered(G))
    print('Core theorem: old regular-core families and K_k-boundary copies verified.')


def critical_hosts(n, k):
    geng = shutil.which('nauty-geng') or shutil.which('geng')
    assert geng
    m = (k - 1) * n // 2 + 1
    eta2 = 2 * m - (k - 1) * n
    mindeg = (k + eta2) // 2
    proc = subprocess.Popen([geng, '-q', '-c', f'-d{mindeg}', str(n), f'{m}:{m}'],
                            stdout=subprocess.PIPE)
    assert proc.stdout is not None
    for line in proc.stdout:
        G = ordered(nx.from_graph6_bytes(line.strip()))
        if old.critical_brute(G, k):
            yield G
    assert proc.wait() == 0


def audit_small_reclassification():
    counts, stronger = Counter(), Counter()
    for n in range(4, 10):
        for k in range(3, n):
            for G in critical_hosts(n, k):
                if nx.k_core(G, k - 1):
                    label = 'core terminal'
                elif nx.is_bipartite(G):
                    label = 'whole-host bipartite terminal'
                else:
                    certs = old.cut_certificates(G, k)
                    if n <= 7:
                        assert certs == old.cut_certificates(G, k, full_search=True)
                    label = old.category(certs, k)
                counts[label] += 1
                stronger['matching-defect block terminal' if label != 'core terminal'
                         and matching_defect_block(G, k) is not None else label] += 1
    expected = Counter({'core terminal': 827, 'whole-host bipartite terminal': 27,
                        'absorption': 9209, 'large-cross terminal only': 1,
                        'cross but no budget': 2638, 'no cross cut': 11964})
    assert counts == expected and sum(counts.values()) == 24666
    print('CORE-FIRST RECLASSIFICATION, all normalized critical hosts through n=9:')
    for key, value in counts.items():
        print(' ', key, value)
    assert stronger == Counter({'core terminal': 827, 'matching-defect block terminal': 17482,
                                'absorption': 2682, 'large-cross terminal only': 1,
                                'cross but no budget': 594, 'no cross cut': 3080})
    print('AFTER THE NEW MATCHING-DEFECT BLOCK TERMINAL:', dict(stronger))
    return counts


def one_apex_cl(G, k, Delta):
    """Exact existence test on ANY subgraph, not just on G itself."""
    for s in G:
        if G.degree(s) < k:
            continue
        Q = G.copy()
        Q.remove_node(s)
        C = set(nx.k_core(Q, k - Delta))
        if len(set(G[s]) & C) >= k:
            assert min(G.subgraph(C).degree(v) for v in C) >= k - Delta
            return s, C
    return None


def colored_core(G, a, b):
    """Enumerate the entire X side; the largest admissible Y then suffices."""
    adj = masks(G)
    full = (1 << len(G)) - 1
    for h in range(a, len(G) - b + 1):
        for X0 in combinations(range(len(G)), h):
            X = sum(1 << v for v in X0)
            Y = sum(1 << v for v in old.vertices(full ^ X)
                    if (adj[v] & X).bit_count() >= a)
            if Y.bit_count() >= b and all((adj[v] & Y).bit_count() >= b for v in X0):
                XX, YY = set(X0), set(old.vertices(Y))
                assert not XX & YY
                assert all(len(set(G[v]) & YY) >= b for v in XX)
                assert all(len(set(G[v]) & XX) >= a for v in YY)
                return XX, YY
    return None


def colored_copy(T, G, cert):
    X, Y = cert
    colors = nx.bipartite.color(T)
    A = {v for v in T if colors[v] == 0}
    B = set(T) - A
    if len(A) > len(B):
        A, B = B, A
    target_side = {v: X if v in A else Y for v in T}
    root = min(T)
    phi = {root: min(target_side[root])}
    for p, x in nx.bfs_edges(T, root):
        fresh = set(G[phi[p]]) & target_side[x] - set(phi.values())
        assert fresh
        phi[x] = min(fresh)
    verify_copy(T, G, phi)


class LocalTriangleFinder:
    """Exact local R_i+S_i lift on positive K_3 blow-up completions of n=10."""
    capacities = ((2, 3, 5), (2, 4, 4), (3, 3, 4))

    def __init__(self, T):
        self.T = T
        assert list(T) == list(range(8))
        self.profiles = {}
        for ws in self.capacities:
            prof = {}
            for h in product(range(3), repeat=8):
                if any(h[u] == h[v] for u, v in T.edges()):
                    continue
                if any(h.count(i) > ws[i] for i in range(3)):
                    continue
                N = tuple(tuple(sorted({tuple(sum(h[v] == j for v in T[u])
                                                       for j in range(3))
                                          for u in T if h[u] == i})) for i in range(3))
                M = tuple(tuple(max((x[j] for x in N[i]), default=0)
                                      for j in range(3)) for i in range(3))
                prof.setdefault((N, M), h)
            self.profiles[ws] = [(N, M, h) for (N, M), h in prof.items()]
        self.test_bounds = lru_cache(None)(self._test_bounds)

    def _test_bounds(self, ws, ds):
        d = [[0, ds[0], ds[1]], [ds[2], 0, ds[3]], [ds[4], ds[5], 0]]
        for N, M, h in self.profiles[ws]:
            R = [max((sum(x[j] * d[j][i] for j in range(3)) for x in N[i]), default=0)
                 for i in range(3)]
            S = [sum(d[i][j] * M[j][i] for j in range(3)) for i in range(3)]
            good = [ws[i] >= R[i] + S[i] for i in range(3)]
            if all(good[i] or good[j] or d[i][j] == 0 for i, j in combinations(range(3), 2)):
                return h, tuple(good)
        return None

    def find(self, G):
        assert len(G) == 10
        adj = masks(G)
        allv = set(G)
        for ws in self.capacities:
            for A in combinations(range(10), ws[0]):
                rem = allv - set(A)
                for B in combinations(sorted(rem), ws[1]):
                    C = tuple(sorted(rem - set(B)))
                    if ws[0] == ws[1] and A > B:
                        continue
                    if ws[1] == ws[2] and B > C:
                        continue
                    blocks = (A, B, C)
                    ms = [sum(1 << v for v in Z) for Z in blocks]
                    d = tuple(len(blocks[j]) - min((adj[v] & ms[j]).bit_count()
                                                     for v in blocks[i])
                              for i in range(3) for j in range(3) if j != i)
                    result = self.test_bounds(ws, d)
                    if result is not None:
                        h, good = result
                        return blocks, h, good
        return None


def verify_and_lift_local(T, G, cert):
    """Independent adjacency-set verification, followed by actual improving swaps."""
    blocks, h, good = cert
    assert set().union(*map(set, blocks)) == set(G)
    assert sum(map(len, blocks)) == len(G)
    Hedges = {tuple(sorted((u, v))) for i, j in combinations(range(3), 2)
              for u in blocks[i] for v in blocks[j]}
    gedges = {tuple(sorted(e)) for e in G.edges()}
    missing_edges, ignored_edges = Hedges - gedges, gedges - Hedges
    assert len(Hedges) > 3 * len(G)
    assert len(missing_edges) >= len(ignored_edges)
    missing = {v: set() for v in G}
    for u, v in missing_edges:
        missing[u].add(v)
        missing[v].add(u)
    d = [[0 if i == j else max(len(missing[v] & set(blocks[j])) for v in blocks[i])
          for j in range(3)] for i in range(3)]
    R, S = [], []
    for i in range(3):
        R.append(max((sum(d[h[v]][i] for v in T[u]) for u in T if h[u] == i), default=0))
        S.append(sum(d[i][j] * max((sum(h[u] == i for u in T[v])
                                    for v in T if h[v] == j), default=0)
                     for j in range(3)))
        assert good[i] == (len(blocks[i]) >= R[i] + S[i])
    assert all(good[i] or good[j] for i, j in combinations(range(3), 2) if d[i][j])
    assert all(h[u] != h[v] for u, v in T.edges())
    phi = {}
    for i in range(3):
        vv = [v for v in T if h[v] == i]
        assert len(vv) <= len(blocks[i])
        phi.update(zip(vv, blocks[i]))
    conflicts = lambda: [(u, v) for u, v in T.edges() if phi[v] in missing[phi[u]]]
    bad = conflicts()
    initial = len(bad)
    steps = 0
    while bad:
        u, v = bad[0]
        if not good[h[u]]:
            u, v = v, u
        i, x = h[u], phi[u]
        assert good[i]
        inv = {x: v for v, x in phi.items()}
        bad1 = {y for y in blocks[i] if any(phi[z] in missing[y] for z in T[u])}
        bad2 = {y for y in blocks[i] if y in inv
                and any(phi[z] in missing[x] for z in T[inv[y]])}
        assert x in bad1 & bad2
        assert len(bad1) <= R[i] and len(bad2) <= S[i]
        candidates = set(blocks[i]) - bad1 - bad2
        assert candidates
        y = min(candidates)
        z = inv.get(y)
        phi[u] = y
        if z is not None:
            assert not T.has_edge(u, z)
            phi[z] = x
        next_bad = conflicts()
        assert len(next_bad) < len(bad)
        bad = next_bad
        steps += 1
    assert steps <= initial
    verify_copy(T, G, phi)
    COUNTS['local quotient lifts verified'] += 1
    COUNTS['local quotient improving swaps'] += steps


def audit_order_ten():
    trees = [ordered(T) for T in nx.nonisomorphic_trees(8)
             if max(dict(T.degree()).values()) == 3
             and sum(d == 3 for _, d in T.degree()) >= 2]
    assert len(trees) == 6
    finders = [LocalTriangleFinder(T) for T in trees]
    host_counts, pair_counts = Counter(), Counter()
    stronger_hosts, stronger_pairs = Counter(), Counter()
    for G in critical_hosts(10, 7):
        if nx.k_core(G, 6):
            host_counts['core terminal'] += 1
            stronger_hosts['core terminal'] += 1
            continue
        block = matching_defect_block(G, 7)
        if one_apex_cl(G, 7, 3):
            host_counts['one-apex CL'] += 1
            stronger_hosts['matching-defect block terminal' if block else 'one-apex CL'] += 1
            continue
        certs = old.cut_certificates(G, 7)
        if any(gap <= 0 or c0 > 3 for _, c0, _, gap in certs):
            host_counts['absorbing/large-cross cut'] += 1
            stronger_hosts['matching-defect block terminal' if block else 'absorbing/large-cross cut'] += 1
            continue
        host_counts['remaining for tree-specific tests'] += 1
        stronger_hosts['matching-defect block terminal' if block else 'remaining for tree-specific tests'] += 1
        by_color = {}
        for T, finder in zip(trees, finders):
            ab = tuple(sorted(Counter(nx.bipartite.color(T).values()).values()))
            if ab not in by_color:
                by_color[ab] = colored_core(G, *ab)
            if by_color[ab] is not None:
                colored_copy(T, G, by_color[ab])
                pair_counts[ab, 'colored core'] += 1
                if not block:
                    stronger_pairs[ab, 'colored core'] += 1
            else:
                cert = finder.find(G)
                assert cert is not None, (nx.to_graph6_bytes(G), nx.to_graph6_bytes(T))
                verify_and_lift_local(T, G, cert)
                pair_counts[ab, 'local degree-two quotient lift'] += 1
                if not block:
                    stronger_pairs[ab, 'local degree-two quotient lift'] += 1
            if block:
                C, (v, outside) = block
                ell, p, S = removable_leaf_for_matching_block(T)
                phi = rooted_matching_block_copy(S, G, C, p, v)
                phi[ell] = outside
                verify_copy(T, G, phi)
                COUNTS['matching-block copies in the former 920-host residue'] += 1
    assert host_counts == Counter({'core terminal': 224, 'one-apex CL': 53087,
                                  'absorbing/large-cross cut': 1531,
                                  'remaining for tree-specific tests': 920})
    assert sum(host_counts.values()) == 55762
    assert sum(pair_counts.values()) == 920 * 6
    print('EXACT ORDER-10, k=7 COVERAGE (six nonspider subcubic trees):')
    print(' Host counts:', dict(host_counts))
    print(' Remaining host/tree pairs:', dict(pair_counts))
    print(' No residual pair after independent local-lift verification.')
    assert stronger_hosts == Counter({'core terminal': 224, 'matching-defect block terminal': 13693,
                                      'one-apex CL': 40915, 'absorbing/large-cross cut': 594,
                                      'remaining for tree-specific tests': 336})
    assert stronger_pairs == Counter({((4, 4), 'colored core'): 522,
                                      ((4, 4), 'local degree-two quotient lift'): 486,
                                      ((3, 5), 'colored core'): 963,
                                      ((3, 5), 'local degree-two quotient lift'): 45})
    assert sum(stronger_pairs.values()) == 336 * 6
    print(' AFTER THE NEW MATCHING-DEFECT BLOCK TERMINAL:')
    print('  Host counts:', dict(stronger_hosts))
    print('  Remaining pairs:', dict(stronger_pairs))


EXAMPLE_R_EDGES = [(0,7),(0,9),(0,11),(1,6),(1,8),(1,10),(2,3),(2,5),(2,9),
                   (2,11),(3,4),(3,11),(3,12),(4,7),(4,10),(4,12),(5,7),
                   (5,9),(5,12),(6,9),(6,10),(6,12),(7,8),(8,10),(8,11)]


def two_tetra_host(r, R=None):
    assert r >= 4
    q = 2 * r - 1
    if R is None:
        R = nx.Graph()
        R.add_nodes_from(range(q))
        R.add_edges_from((i, (i + d) % q) for i in range(q) for d in (1, 2))
        R.remove_edge(0, 1)
    assert set(R) == set(range(q))
    assert all(R.degree(v) == (3 if v < 2 else 4) for v in R)
    D = nx.Graph()
    D.add_nodes_from(range(q + 6))
    D.add_edges_from(R.edges())
    P, Q = list(range(q, q + 3)), list(range(q + 3, q + 6))
    D.add_edges_from(combinations([0] + P, 2))
    D.add_edges_from(combinations([1] + Q, 2))
    return ordered(nx.complement(D)), P, Q, R


def verify_peeling(G, seq, bound):
    assert set(seq) == set(G) and len(seq) == len(G)
    left = set(G)
    for v in seq:
        assert len(set(G[v]) & left) <= bound
        left.remove(v)
    COUNTS['explicit degeneracy orders'] += 1


def audit_core_free_family():
    for r in range(4, 21):
        G, P, Q, R = two_tetra_host(r)
        k = 2 * r + 1
        assert len(G) == 2 * r + 5 and G.number_of_edges() == r * len(G) + 1
        assert set(v for v in G if G.degree(v) >= k) == set(P + Q)
        assert all(G.degree(v) == k for v in P + Q)
        assert G.degree(0) == G.degree(1) == k - 3
        assert not nx.k_core(G, k - 1)
        assert not old.cut_certificates(G, k)
        assert one_apex_cl(G, k, 3) is None
        # Full criticality: only deletions of 1, 2, or 3 vertices need checking.
        for t in (1, 2, 3):
            assert t * (2 * r - 2) - t * (t - 1) // 2 >= r * t + 1
        if r <= 6:
            assert old.critical_brute(G, k)
        if r >= 6:
            Z = [v for v in range(2, len(R)) if v not in R[0] and v not in R[1]]
            assert len(Z) >= 2
            prefix = [0, 1] + Z[:2] + P + Q
            seq = prefix + sorted(set(G) - set(prefix))
            verify_peeling(G, seq, k - 3)
            assert max(nx.core_number(G).values()) == k - 3
        if r >= 5:
            assert len(G) <= 3 * r  # no positive degree-two quotient completion
    # This particular host blocks several tests, but IS near-biclique terminal.
    R = nx.Graph()
    R.add_nodes_from(range(13))
    R.add_edges_from(EXAMPLE_R_EDGES)
    G, P, Q, R = two_tetra_host(7, R)
    assert old.critical_brute(G, 15)
    old.orientation_certificate(G, 7, 0)
    assert colored_core(G, 8, 8) is None
    X, Y = {0,2,3,4,11,13,14,15}, {1,5,6,8,10,16,17,18}
    missing = {(u, v) for u in X for v in Y if not G.has_edge(u, v)}
    assert missing == {(2,5), (4,10), (11,8)}
    assert len(X) == len(Y) == 8 and not X & Y
    assert max(sum(not G.has_edge(v, w) for w in Y) for v in X) == 1
    assert max(sum(not G.has_edge(v, w) for w in X) for v in Y) == 1
    assert max(len(set(G[u]) & set(G[v])) for u, v in combinations(G, 2)) == 15
    print('Core-free no-cut family: r=4..20; exact (k-3)-degeneracy for r>=6.')
    print('Explicit k=15 example: no (8,8)-colored core, but K_8,8 minus a 3-edge matching.')
    print(' Near-biclique sides:', sorted(X), sorted(Y), 'missing:', sorted(missing))
    print(' This host is TERMINAL by the asymmetric Hall bound, not uncovered.')


def audit_high_internal_terminal():
    # Matching-cone kills the old regular core, but not its high K_{r,r}.
    for r in range(3, 6):
        G, U, V, p, q, w = old.regular_core_host(r, 'rook')
        x = len(G)
        M = [(p, q)] + [(w(0, 0, j), w(1, 0, j)) for j in range(r - 1)]
        assert len({v for e in M for v in e}) == 2 * r
        G.remove_edges_from(M)
        G.add_edges_from((x, v) for e in M for v in e)
        G = ordered(G)
        k = 2 * r + 1
        assert not nx.k_core(G, k - 1)
        assert not old.cut_certificates(G, k)
        old.orientation_certificate(G, r, p)
        for T in nx.nonisomorphic_trees(k + 1):
            colors = nx.bipartite.color(T)
            I = {v for v in T if T.degree(v) > 1}
            phi = {}
            for b, targets in enumerate((U, V)):
                ii = [v for v in I if colors[v] == b]
                assert 2 * len(ii) <= k
                phi.update(zip(ii, targets))
            assert len(phi) == len(I)
            for ell in T:
                if ell in I:
                    continue
                parent = next(iter(T[ell]))
                assert parent in I and G.degree(phi[parent]) >= k
                fresh = set(G[phi[parent]]) - set(phi.values())
                assert fresh
                phi[ell] = min(fresh)
            verify_copy(T, G, phi)
            COUNTS['high-internal-core copies'] += 1
    print('New high-internal-core lemma: core-free matching-cone hosts are terminal too.')


def audit_example_hall_copy():
    R = nx.Graph()
    R.add_nodes_from(range(13))
    R.add_edges_from(EXAMPLE_R_EDGES)
    G, *_ = two_tetra_host(7, R)
    X, Y = {0,2,3,4,11,13,14,15}, {1,5,6,8,10,16,17,18}
    # Exhaust every candidate uniform near-clique block, not just all of G.
    for N in range(16, 20):
        for S in combinations(G, N):
            d = max(N - 1 - sum(G.has_edge(v, w) for w in S) for v in S)
            assert N < 6 * d
            COUNTS['near-clique blocks excluded in example'] += 1
    T = nx.Graph()
    T.add_nodes_from(range(16))
    T.add_edges_from([(0,1),(0,2),(2,3),(3,4),(0,5),(5,6),(6,7),(7,8),
                      (1,9),(9,10),(10,11),(1,12),(12,13),(13,14),(14,15)])
    colors = nx.bipartite.color(T)
    A = {v for v in T if colors[v] == 0}
    B = set(T) - A
    assert len(A) == len(B) == 8 and max(dict(T.degree()).values()) == 3
    assert sum(T.degree(v) == 3 for v in T) == 2
    assert max(dict(T.subgraph(v for v in T if T.degree(v) > 1).degree()).values()) == 3
    phi = dict(zip(sorted(B), sorted(Y)))
    M = nx.Graph()
    left = {('tree', u) for u in A}
    M.add_nodes_from(left, bipartite=0)
    M.add_nodes_from({('host', x) for x in X}, bipartite=1)
    for u in A:
        for x in X:
            if all(G.has_edge(x, phi[v]) for v in T[u]):
                M.add_edge(('tree', u), ('host', x))
    matching = nx.bipartite.maximum_matching(M, top_nodes=left)
    assert left <= matching.keys()
    phi.update({u: matching['tree', u][1] for u in A})
    assert set(phi.values()) == X | Y
    verify_copy(T, G, phi)
    print('Explicit noncaterpillar subcubic T_16: zero-spare-capacity Hall copy:', phi)


def near_clique_copy(T, G, S, root_pair=None):
    """Sauer swaps, optionally preserving one prescribed image.

    The strict sufficient bound is |S| > 2*Delta(T)*d + number_of_fixed_vertices.
    A chosen conflicted edge's other endpoint is excluded explicitly; this also
    handles swaps between adjacent pattern vertices without treating loops as
    complement edges.
    """
    S = set(S)
    D = {v: S - {v} - set(G[v]) for v in S}
    Delta = max(dict(T.degree()).values(), default=0)
    d = max(map(len, D.values()), default=0)
    assert len(T) <= len(S) and len(S) > 2 * Delta * d + bool(root_pair)
    fixed = {} if root_pair is None else dict([root_pair])
    assert set(fixed) <= set(T) and set(fixed.values()) <= S
    phi = dict(fixed)
    phi.update(zip(sorted(set(T) - set(fixed)), sorted(S - set(fixed.values()))))
    conflicts = lambda: [(u, v) for u, v in T.edges() if phi[v] in D[phi[u]]]
    bad = conflicts()
    steps = 0
    while bad:
        u, v = bad[0]
        if u in fixed:
            u, v = v, u
        assert u not in fixed
        x = phi[u]
        inv = {y: z for z, y in phi.items()}
        B1 = {y for y in S if any(phi[w] in D[y] for w in T[u])}
        B2 = {y for y in S if y in inv and any(phi[w] in D[x] for w in T[inv[y]])}
        assert x in B1 & B2 and len(B1) <= Delta * d and len(B2) <= Delta * d
        candidates = S - B1 - B2 - {phi[v]} - set(fixed.values())
        assert candidates
        y = min(candidates)
        z = inv.get(y)
        phi[u] = y
        if z is not None:
            assert z not in fixed
            phi[z] = x
        next_bad = conflicts()
        assert len(next_bad) < len(bad)
        assert all(phi[w] == yy for w, yy in fixed.items())
        bad = next_bad
        steps += 1
    verify_copy(T, G, phi)
    COUNTS['near-clique improving swaps'] += steps
    COUNTS['root-preserving near-clique copies' if fixed else 'unrooted near-clique copies'] += 1
    return phi


def audit_large_two_tetra_terminal():
    import random
    rng = random.Random(548)
    for r in range(11, 21):
        G, *_ = two_tetra_host(r)
        k = 2 * r + 1
        S = set(G) - {0, 1}
        assert len(S) == k + 2 and max(len(S - {v} - set(G[v])) for v in S) <= 4
        assert len(S) > 24
        # Delta >= 4 is already covered by CL; test Delta=4 exactly.
        assert one_apex_cl(G, k, 4) is not None
        for _ in range(10):
            # Each label occurs at most twice, hence the resulting tree is subcubic.
            T = nx.from_prufer_sequence(rng.sample(list(range(k + 1)) * 2, k - 1))
            assert max(dict(T.degree()).values()) <= 3
            near_clique_copy(T, G, S)
    print('Two-tetra family for every r>=11: CL handles Delta>=4; a near-clique handles Delta<=3.')


def modular_host(r):
    """A critical (k-2)-degenerate no-cut family that is nevertheless universal."""
    assert r >= 5
    k = 2 * r + 1
    Q = nx.disjoint_union(nx.complete_graph(k), nx.complete_graph(k))
    blocks = [list(range(k)), list(range(k, 2 * k))]
    H = [[[], [], []], [[], [], []]]
    for j, h in enumerate((r, r - 1, r)):
        h0 = (h + j % 2) // 2
        for b, count in enumerate((h0, h - h0)):
            start = blocks[b][0] + sum(map(len, H[b]))
            H[b][j] = list(range(start, start + count))
    ordinary = [sorted(set(blocks[b]) - set(sum(H[b], []))) for b in range(2)]
    a, b = ordinary[0][:2]
    c, d = ordinary[1][:2]
    Q.remove_edges_from([(a, b), (c, d)])
    Q.add_edges_from([(a, c), (b, d)])
    assert nx.is_connected(Q) and set(dict(Q.degree()).values()) == {2 * r}
    G = Q.copy()
    L = [2 * k, 2 * k + 1, 2 * k + 2]
    G.add_edges_from(zip(L, L[1:]))
    for j, ell in enumerate(L):
        G.add_edges_from((ell, v) for b in range(2) for v in H[b][j])
    candidates = []
    for b in range(2):
        pairs = []
        for j in range(3):
            pairs.extend(zip(H[b][j][::2], H[b][j][1::2]))
        pairs.extend(zip(ordinary[b][2::2], ordinary[b][3::2]))
        candidates.append(pairs)
    from itertools import zip_longest
    pairs = [e for pair in zip_longest(*candidates) for e in pair if e is not None]
    M = [tuple(L[:2])] + pairs[:r - 1]
    assert len(M) == r and len({v for e in M for v in e}) == 2 * r
    x = len(G)
    G.remove_edges_from(M)
    G.add_edges_from((x, v) for e in M for v in e)
    return ordered(G), blocks, H, L, x, M


def audit_modular_family():
    targets = Counter()
    for r in range(5, 21):
        G, blocks, types, L, x, M = modular_host(r)
        k = 2 * r + 1
        H = set(sum(types[0] + types[1], []))
        assert len(G) == 4 * r + 6 and G.number_of_edges() == r * len(G) + 1
        assert H == {v for v in G if G.degree(v) >= k}
        assert all(G.degree(v) == k for v in H)
        assert all(G.degree(v) == r + 1 for v in L) and G.degree(x) == 2 * r
        assert not nx.k_core(G, 2 * r)
        assert max(nx.core_number(G).values()) == 2 * r - 1
        assert all(set(G[v]) & H for v in G)
        assert one_apex_cl(G, k, r) is None
        # Exact cut test via all independent sets of the two high blocks.
        # A high vertex is saturated, so no other A can satisfy d_B >= k.
        indeps = []
        for b in range(2):
            HH = set(sum(types[b], []))
            assert all(len(HH - {v} - set(G[v])) <= 1 for v in HH)
            ii = [set()] + [{v} for v in HH]
            ii += [{u, v} for u, v in combinations(HH, 2) if not G.has_edge(u, v)]
            for A in ii:
                assert sum(bool(A & set(Z)) for Z in types[b]) <= 1
            indeps.append(ii)
        for A0, A1 in product(*indeps):
            A = A0 | A1
            if A:
                assert all(len(set(G[v]) - A) == k for v in A)
                assert any(not set(G[ell]) & A for ell in L)
                COUNTS['modular independent-cut exclusions'] += 1
        if r <= 7:
            assert not old.cut_certificates(G, k)
            old.orientation_certificate(G, r, 0)
        # The actual terminal dichotomy, not an uncovered-family claim.
        C = blocks[1]
        assert max(len(set(C) - {v} - set(G[v])) for v in C) == 1
        B = max((set(sum(Z, [])) for Z in types), key=len)
        assert len(B) >= r + 3
        assert min(len(set(G[v]) & B) for v in B) >= len(B) - 2 >= r + 1
        if r > 7:
            continue
        for T in nx.nonisomorphic_trees(k + 1):
            Delta = max(dict(T.degree()).values())
            if Delta <= r - 1:
                ell = next(v for v in T if T.degree(v) == 1)
                p = next(iter(T[ell]))
                outside = L[0]
                parent_image = min(set(G[outside]) & set(C))
                S = T.copy()
                S.remove_node(ell)
                phi = near_clique_copy(S, G, C, (p, parent_image))
                phi[ell] = outside
                label = 'rooted near-clique plus outside leaf'
            else:
                I = {v for v in T if T.degree(v) > 1}
                assert len(I) <= r + 2
                phi = grow(T.subgraph(I), G.subgraph(B), {min(I): min(B)})
                for ell in set(T) - I:
                    p = next(iter(T[ell]))
                    assert G.degree(phi[p]) >= k
                    phi[ell] = min(set(G[phi[p]]) - set(phi.values()))
                label = 'high-internal tree'
            verify_copy(T, G, phi)
            targets[label] += 1
    assert sum(targets.values()) == 23030
    print('Modular no-cut family: exact (k-2)-degeneracy for r=5..20; terminal for every r>=5.')
    print(' All 23,030 target trees at r=5,6,7 embedded:', dict(targets))


def spanning_star(F):
    return len(F) >= 2 and any(d == len(F) - 1 for _, d in F.degree())


def complement_forest_matching(F):
    """A maximum complement matching, with the forest theorem checked directly."""
    assert len(F) and nx.is_forest(F)
    M = [tuple(sorted(e)) for e in nx.max_weight_matching(nx.complement(F), maxcardinality=True)]
    M.sort()
    assert len({v for e in M for v in e}) == 2 * len(M)
    assert all(not F.has_edge(u, v) and u != v for u, v in M)
    expected = len(F) // 2 - (len(F) % 2 == 0 and spanning_star(F))
    assert len(M) == expected
    if len(F) % 2 == 0 and spanning_star(F):
        s = next(v for v in F if F.degree(v) == len(F) - 1)
        assert nx.complement(F).degree(s) == 0
    COUNTS['complement-forest matching certificates'] += 1
    return M


def removable_leaf_for_matching_block(T):
    """The diameter-case lemma supplies such a leaf for every nonstar k>=4."""
    k = T.number_of_edges()
    assert nx.is_tree(T) and k >= 4 and not spanning_star(T)
    for ell in T:
        if T.degree(ell) != 1:
            continue
        p = next(iter(T[ell]))
        S = T.copy()
        S.remove_node(ell)
        if spanning_star(S):
            continue
        if k % 2:
            F = S.copy()
            F.remove_node(p)
            if spanning_star(F):
                continue
        return ell, p, S
    raise AssertionError('diameter-case leaf selection failed')


def rooted_matching_block_copy(S, G, C, p, v):
    """Rooted packing by nonedge matchings, not tree-embedding backtracking."""
    C = sorted(C)
    N = len(C)
    assert nx.is_tree(S) and len(S) == N and N >= 4 and not spanning_star(S)
    assert p in S and v in C
    host_M = [e for e in combinations(C, 2) if not G.has_edge(*e)]
    assert len({x for e in host_M for x in e}) == 2 * len(host_M)
    host_pair = next((e for e in host_M if v in e), None)
    phi = {}
    if host_pair is not None:
        M = complement_forest_matching(S)
        assert len(M) == N // 2
        pair = next((e for e in M if p in e), None)
        if pair is None:
            assert N % 2
            # Move the unique unmatched position away from p.
            q = next(q for q in S if q != p and not S.has_edge(p, q))
            qr = next(e for e in M if q in e)
            M.remove(qr)
            pair = tuple(sorted((p, q)))
            M.append(pair)
        pp = next(w for w in pair if w != p)
        vv = next(w for w in host_pair if w != v)
        phi = {p: v, pp: vv}
        M.remove(pair)
        remaining_host = [e for e in host_M if e != host_pair]
    else:
        F = S.copy()
        F.remove_node(p)
        if N % 2:
            assert not spanning_star(F)
        M = complement_forest_matching(F)
        phi = {p: v}
        remaining_host = host_M
    assert len(M) >= len(remaining_host)
    for pair, image_pair in zip(M, remaining_host):
        phi.update(zip(pair, image_pair))
    phi.update(zip(sorted(set(S) - set(phi)), sorted(set(C) - set(phi.values()))))
    assert phi[p] == v
    verify_copy(S, G, phi)
    return phi


def matching_defect_block(G, k):
    """Exact k-vertex clique-minus-matching terminal, valid for k>=4."""
    if k < 4:
        return None
    adj = masks(G)
    for C in combinations(range(len(G)), k):
        Z = sum(1 << v for v in C)
        if all((adj[v] & Z).bit_count() >= k - 2 for v in C):
            # A critical connected host has a boundary, but verify it explicitly.
            boundary = next(((v, w) for v in C for w in G[v] if not Z & (1 << w)), None)
            if boundary is not None:
                return set(C), boundary
    return None


def audit_matching_block_terminal():
    for F in nx.graph_atlas_g():
        if len(F) and nx.is_forest(F):
            complement_forest_matching(F)
    totals = Counter()
    for k in range(4, 13):
        hosts = []
        for m in range(k // 2 + 1):
            C = nx.complete_graph(k)
            C.remove_edges_from((2 * i, 2 * i + 1) for i in range(m))
            roots = ([0] if m else []) + ([2 * m] if 2 * m < k else [])
            for v in roots:
                G = C.copy()
                G.add_edge(v, k)
                hosts.append((ordered(G), v, m))
        assert len(hosts) == k  # all matching sizes and boundary-vertex orbits
        for T in nx.nonisomorphic_trees(k + 1):
            if spanning_star(T):
                continue
            ell, p, S = removable_leaf_for_matching_block(T)
            totals['nonstar targets'] += 1
            for G, v, m in hosts:
                assert matching_defect_block(G, k) is not None
                phi = rooted_matching_block_copy(S, G, range(k), p, v)
                phi[ell] = k
                verify_copy(T, G, phi)
                totals['full target copies'] += 1
    assert totals == Counter({'nonstar targets': 2274, 'full target copies': 25550})
    print('Stronger matching-defect k-block terminal (k>=4):', dict(totals))
    print(' Every matching size and boundary-vertex orbit checked for 4<=k<=12.')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--skip-order-ten', action='store_true')
    args = parser.parse_args()
    start = time.time()
    audit_core_terminal()
    audit_small_reclassification()
    audit_core_free_family()
    audit_high_internal_terminal()
    audit_example_hall_copy()
    audit_large_two_tetra_terminal()
    audit_modular_family()
    audit_matching_block_terminal()
    if not args.skip_order_ten:
        audit_order_ten()
    print('VERIFICATION COUNTS:', dict(COUNTS))
    print('PASS. No global extraction/coverage assertion. Seconds:', round(time.time() - start, 2))


if __name__ == '__main__':
    main()
