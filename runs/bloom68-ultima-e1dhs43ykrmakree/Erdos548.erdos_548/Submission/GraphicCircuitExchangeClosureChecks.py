#!/usr/bin/env python3
"""Exact construction audits for GraphicCircuitExchangeClosure.md.

Finite checks are NOT a proof of GC_r or Erdos--Sos.  No old source is edited.
Only Python's standard library and networkx are used.
"""
from __future__ import annotations

from collections import Counter, deque
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import random
import time

import networkx as nx

HERE = Path(__file__).resolve().parent
SPEC_SHA = "674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103"
RNG = random.Random(740531)
COUNTS = Counter()


def edge(u, v):
    return tuple(sorted((u, v)))


def edges(G):
    return {edge(u, v) for u, v in G.edges()}


def graph(n, E):
    G = nx.Graph()
    G.add_nodes_from(range(n))
    G.add_edges_from(E)
    return G


def subset_counts(G):
    n = len(G)
    assert set(G) == set(range(n))
    adj = [sum(1 << v for v in G[u]) for u in range(n)]
    ec = [0] * (1 << n)
    for S in range(1, 1 << n):
        bit = S & -S
        v = bit.bit_length() - 1
        rest = S ^ bit
        ec[S] = ec[rest] + (adj[v] & rest).bit_count()
    return ec


def mask_set(S):
    return {v for v in range(S.bit_length()) if (S >> v) & 1}


def check_circuit(C, r):
    n = len(C)
    E = subset_counts(C)
    full = (1 << n) - 1
    assert E[full] == r * (n - 1) + 1
    for S in range(1, full):
        assert E[S] <= r * (S.bit_count() - 1), (r, n, S)
    assert nx.is_biconnected(C)
    # Independent induced-edge recount on deterministic sampled subsets.
    for _ in range(min(40, full - 1)):
        S = RNG.randrange(1, full)
        V = mask_set(S)
        assert E[S] == sum(u in V and v in V for u, v in C.edges())
        COUNTS['independent_subset_recounts'] += 1
    COUNTS['proper_subset_inequalities'] += full - 1
    COUNTS['circuits'] += 1
    return E


def spanning_partition(C, B, f):
    assert f not in set().union(*B)
    assert set().union(*B, {f}) == edges(C)
    assert sum(map(len, B)) == len(set().union(*B))
    assert all(nx.is_tree(graph(len(C), F)) for F in B)


def path_edges(B, u, v):
    path = nx.shortest_path(B, u, v)
    return [edge(a, b) for a, b in zip(path, path[1:])]


def frozen_exchange(C, B):
    BG = [graph(len(C), F) for F in B]
    D = {e: set() for e in edges(C)}
    colors = {e: i for i, F in enumerate(B) for e in F}
    for e in D:
        for i, F in enumerate(B):
            if e not in F:
                D[e].update(path_edges(BG[i], *e))
    return D, colors


def move_hole(C, B, f, g, D, colors):
    pred = {f: None}
    todo = deque([f])
    while todo and g not in pred:
        e = todo.popleft()
        for h in sorted(D[e]):
            if h not in pred:
                pred[h] = e
                todo.append(h)
    assert g in pred
    P = []
    cur = g
    while cur is not None:
        P.append(cur)
        cur = pred[cur]
    P.reverse()
    assert P[0] == f and P[-1] == g and len(P) == len(set(P))
    for a in range(len(P)):
        for b in range(a + 2, len(P)):
            assert P[b] not in D[P[a]]
    current = [set(F) for F in B]
    hole = f
    for j in range(1, len(P)):
        incoming, outgoing = P[j - 1], P[j]
        i = colors[outgoing]
        assert hole == incoming and outgoing in current[i]
        assert incoming not in set().union(*current)
        original_cut_graph = graph(len(C), B[i] - {outgoing})
        components = list(nx.connected_components(original_cut_graph))
        assert len(components) == 2
        A = components[0]
        crosses = lambda e: (e[0] in A) != (e[1] in A)
        assert crosses(incoming)
        assert {e for e in current[i] if crosses(e)} == {outgoing}
        actual_path = path_edges(graph(len(C), current[i]), *incoming)
        assert outgoing in actual_path
        current[i].add(incoming)
        current[i].remove(outgoing)
        hole = outgoing
        spanning_partition(C, current, hole)
        COUNTS['verified_exchange_steps'] += 1
    assert hole == g
    COUNTS['hole_relocations'] += 1
    return current


def close_paths(BG, start):
    S = set(start)
    while True:
        new = set(S)
        anchor = min(S)
        for B in BG:
            for v in S:
                new.update(nx.shortest_path(B, anchor, v))
        if new == S:
            return S
        S = new


def random_base_plus_edge(r, n):
    # Random spanning trees chosen from successively unused edges of K_n.
    # Failed choices are retried; no failure is treated as a negative result.
    for attempt in range(1000):
        available = nx.complete_graph(n)
        B = []
        for _ in range(r):
            if not nx.is_connected(available):
                break
            for u, v in available.edges():
                available[u][v]['weight'] = RNG.random()
            F = edges(nx.minimum_spanning_tree(available))
            B.append(F)
            available.remove_edges_from(F)
        if len(B) == r and available.number_of_edges():
            f = RNG.choice(sorted(edges(available)))
            return B, f
    raise AssertionError('random base generation retry budget exhausted')


def extracted_circuit(r, n):
    B, f = random_base_plus_edge(r, n)
    BG = [graph(n, F) for F in B]
    U = close_paths(BG, f)
    relabel = {u: j for j, u in enumerate(sorted(U))}
    B2 = [{edge(relabel[u], relabel[v]) for u, v in F if u in U and v in U}
          for F in B]
    f2 = edge(*(relabel[u] for u in f))
    C = graph(len(U), set().union(*B2, {f2}))
    spanning_partition(C, B2, f2)
    COUNTS['fundamental_circuit_extractions'] += 1
    return C, B2, f2


def multigraph_contraction(C, S):
    outside = sorted(set(C) - S)
    labels = {v: j + 1 for j, v in enumerate(outside)}
    for v in S:
        labels[v] = 0
    Q = nx.MultiGraph()
    Q.add_nodes_from(range(len(outside) + 1))
    for u, v in C.edges():
        a, b = labels[u], labels[v]
        if a != b:
            Q.add_edge(a, b)
    return Q


def audit_tight_sets(C, r, ec):
    n = len(C)
    full = (1 << n) - 1
    tight = [S for S in range(1, full)
             if ec[S] == r * (S.bit_count() - 1)]
    for M in tight:
        S = mask_set(M)
        assert nx.is_connected(C.subgraph(set(C) - S))
        if len(S) == 1:
            continue
        Q = multigraph_contraction(C, S)
        qn = len(Q)
        assert Q.number_of_edges() == r * (qn - 1) + 1
        for W in range(1, (1 << qn) - 1):
            V = mask_set(W)
            count = sum(u in V and v in V for u, v in Q.edges())
            assert count <= r * (len(V) - 1)
        if n - len(S) >= 2:
            for z in set(C) - S:
                assert len(set(C[z]) & S) <= r
        COUNTS['tight_contractions'] += 1
    for _ in range(70):
        M = RNG.randrange(1, full)
        S, R = mask_set(M), mask_set(full ^ M)
        a = r * (len(S) - 1) - ec[M]
        b = r * (len(R) - 1) - ec[full ^ M]
        cross = sum((u in S) != (v in S) for u, v in C.edges())
        assert cross == r + 1 + a + b
        components = list(nx.connected_components(C.subgraph(R)))
        if len(components) >= 2:
            lhs = sum(r * (len(S | D) - 1) - C.subgraph(S | D).number_of_edges()
                      for D in components)
            assert lhs == (len(components) - 1) * a - 1
            if a == 1:
                assert sum(C.subgraph(S | D).number_of_edges() == r * (len(S | D)-1)
                           for D in components) >= 2
            COUNTS['separator_identities'] += 1
        COUNTS['cut_identities'] += 1
    # Exact neighborhood-hull characterization for every degree-(r+1) vertex.
    for v in C:
        if C.degree(v) != r + 1:
            continue
        Hverts = set(C) - {v}
        A = set(C[v])
        Hmask = full ^ (1 << v)
        assert ec[Hmask] == r * (n - 2)
        Htight = [mask_set(S) for S in tight if not ((S >> v) & 1)]
        assert Hverts in Htight
        assert all(not A <= S for S in Htight if S != Hverts)
        for a in A:
            union = set()
            for b in A - {a}:
                hull = set(Hverts)
                for S in Htight:
                    if {a, b} <= S:
                        hull &= S
                assert hull in Htight
                union |= hull
            assert union == Hverts
        COUNTS['degree_r_plus_one_interfaces'] += 1


def audit_components(C, r, B, f, ec):
    n = len(C)
    full = (1 << n) - 1
    BG = [graph(n, F) for F in B]
    bcounts = [subset_counts(F) for F in BG]
    for S in range(1, full):
        size = S.bit_count()
        epsilon = int(all((S >> v) & 1 for v in f))
        component_excess = sum(size - be[S] - 1 for be in bcounts)
        slack = r * (size - 1) - ec[S]
        assert component_excess == slack + epsilon
    for _ in range(60):
        S = RNG.randrange(1, full)
        V = mask_set(S)
        cc = [nx.number_connected_components(F.subgraph(V)) for F in BG]
        eps = int(set(f) <= V)
        slack = r * (len(V) - 1) - ec[S]
        assert sum(x - 1 for x in cc) == slack + eps
        assert all(x == 1 for x in cc) == (slack == 0 and eps == 0)
        COUNTS['direct_component_counts'] += 1
    assert close_paths(BG, f) == set(C)
    COUNTS['component_identity_subsets'] += full - 1


def injective_embedding(P, H, allowed=None):
    allowed = allowed or {}
    used = set()
    f = {}
    domains = {u: {x for x in H if H.degree(x) >= P.degree(u)} &
                  set(allowed.get(u, H)) for u in P}

    def dfs():
        if len(f) == len(P):
            return dict(f)
        choices = []
        for u in P:
            if u in f:
                continue
            candidates = domains[u] - used
            assigned = [w for w in P[u] if w in f]
            for w in assigned:
                candidates &= set(H[f[w]])
            if not candidates:
                return None
            choices.append((len(candidates), -len(assigned), -P.degree(u), u, candidates))
        _, _, _, u, candidates = min(choices, key=lambda z: z[:4])
        for x in sorted(candidates):
            f[u] = x
            used.add(x)
            ans = dfs()
            if ans is not None:
                return ans
            used.remove(x)
            del f[u]
        return None

    return dfs()


def verify_map(T, G, f):
    assert set(f) == set(T)
    assert len(set(f.values())) == len(T)
    assert set(f.values()) <= set(G)
    assert all(G.has_edge(f[u], f[v]) for u, v in T.edges())


def boundary_map(T, r, p, J, x):
    k = 2 * r + 1
    d = T.degree(p)
    nonleaves = {u for u in T if T.degree(u) > 1}
    un = set(T[p]) & nonleaves
    assert len(un) == 1
    u = next(iter(un))
    leaves = sorted(set(T[p]) - {u})
    assert all(T.degree(z) == 1 for z in leaves)
    R = T.subgraph(set(T) - {p} - set(leaves)).copy()
    m = len(R)
    q = k * (k - 1) // 2 - J.number_of_edges()
    assert q <= 2 * r - d and m == 2 * r + 2 - d
    assert nx.is_tree(R) and max(dict(R.degree()).values()) <= m - 2
    bad = set(J) - {x} - set(J[x])
    t = len(bad)
    assert J.degree(x) >= d
    reserve = sorted(J[x])[:d - 2]
    K = J.subgraph(set(J) - {x} - set(reserve)).copy()
    qK = m * (m - 1) // 2 - K.number_of_edges()
    assert bad <= set(K)
    assert qK <= q - t
    assert R.number_of_edges() + qK + t <= 2 * m - 3
    f = injective_embedding(R, K, {u: set(K) - bad})
    assert f is not None
    y = k
    G = J.copy()
    G.add_edge(x, y)
    f[p] = x
    f[leaves[0]] = y
    for leaf, z in zip(leaves[1:], reserve):
        f[leaf] = z
    verify_map(T, G, f)
    COUNTS['boundary_embeddings'] += 1
    if q == 2 * r - d:
        COUNTS['boundary_max_budget_embeddings'] += 1
    if q >= r:
        COUNTS['boundary_beyond_old_budget'] += 1


def multi_boundary_map(T, r, parents, missing):
    t = len(parents)
    degrees = [T.degree(p) for p in parents]
    D = sum(degrees)
    Delta = max(dict(T.degree()).values())
    assert D + Delta <= 2 * r
    size = 2 * r + 2 - t
    J = nx.complete_graph(size)
    J.remove_edges_from(missing)
    q = len(missing)
    assert q <= 2*r-D
    X = set(range(t))
    reserves = []
    used = set(X)
    leaves = []
    attachments = []
    deleted = set(parents)
    for i, p in enumerate(parents):
        leaf = sorted(v for v in T[p] if T.degree(v) == 1)
        attachment = set(T[p]) - set(leaf)
        assert len(attachment) == 1 and len(leaf) == degrees[i] - 1
        leaves.append(leaf)
        attachments.append(next(iter(attachment)))
        deleted.update(leaf)
        available = sorted(set(J[i]) - used)
        assert len(available) >= degrees[i] - 2
        reserve = available[:degrees[i]-2]
        reserves.append(reserve)
        used.update(reserve)
    assert all(u not in parents for u in attachments)
    R = T.subgraph(set(T)-deleted).copy()
    K = J.subgraph(set(J)-used).copy()
    m = 2*r+2-D
    assert len(R) == len(K) == m and nx.is_tree(R)
    assert max(dict(R.degree()).values()) <= m-2
    prohibitions = set()
    for i, u in enumerate(attachments):
        prohibitions.update((u, b) for b in K if not J.has_edge(i, b))
    qK = m*(m-1)//2-K.number_of_edges()
    assert qK + len(prohibitions) <= q
    assert R.number_of_edges()+qK+len(prohibitions) <= 2*m-3
    allowed = {u: set(K) for u in set(attachments)}
    for u, b in prohibitions:
        allowed[u].discard(b)
    f = injective_embedding(R, K, allowed)
    assert f is not None
    G = J.copy()
    for i, p in enumerate(parents):
        y = size+i
        G.add_edge(i, y)
        f[p] = i
        f[leaves[i][0]] = y
        for leaf, z in zip(leaves[i][1:], reserves[i]):
            f[leaf] = z
    verify_map(T, G, f)
    COUNTS['multi_boundary_embeddings'] += 1
    COUNTS[f'boundary_matching_size_{t}_embeddings'] += 1
    if len(set(attachments)) < len(attachments):
        COUNTS['coincident_attachment_multi_boundary_embeddings'] += 1


def audit_boundary_and_clique():
    for r in range(2, 6):
        k = 2 * r + 1
        trees = []
        for T0 in nx.nonisomorphic_trees(k + 1):
            T = nx.convert_node_labels_to_integers(T0)
            if max(dict(T.degree()).values()) <= r:
                trees.append(T)
        for T in trees:
            internal = {u for u in T if T.degree(u) > 1}
            ends = [u for u in internal if len(set(T[u]) & internal) == 1]
            p = min(ends, key=lambda u: (T.degree(u), u))
            d = T.degree(p)
            assert 2 <= d <= r
            qmax = 2 * r - d
            all_pairs = list(combinations(range(k), 2))
            x = 0
            incident = [e for e in all_pairs if x in e]
            away = [e for e in all_pairs if x not in e]
            patterns = [incident[:qmax], away[:qmax], RNG.sample(all_pairs, qmax),
                        RNG.sample(all_pairs, r)]
            for missing in patterns:
                J = nx.complete_graph(k)
                J.remove_edges_from(missing)
                boundary_map(T, r, p, J, x)
            ordered_ends = sorted(ends, key=lambda u: (T.degree(u), u))
            for t in range(2, len(ordered_ends)+1):
                parents = ordered_ends[:t]
                D = sum(T.degree(p) for p in parents)
                if D + max(dict(T.degree()).values()) > 2*r:
                    break
                size = 2*r+2-t
                q = 2*r-D
                pairs = list(combinations(range(size), 2))
                incident_zero = [e for e in pairs if 0 in e]
                for missing in [incident_zero[:q], RNG.sample(pairs, q)]:
                    multi_boundary_map(T, r, parents, missing)
            # Explicit two-matching clique embedding, on a 2-connected ear host.
            G = nx.complete_graph(2 * r)
            y1, y2 = 2 * r, 2 * r + 1
            G.add_edges_from([(0, y1), (y1, y2), (y2, 1)])
            assert nx.is_biconnected(G)
            p1, p2 = ends[0], ends[-1]
            assert p1 != p2
            l1 = next(z for z in T[p1] if T.degree(z) == 1)
            l2 = next(z for z in T[p2] if T.degree(z) == 1)
            remaining = set(T) - {l1, l2}
            f = {p1: 0, p2: 1}
            for a, b in zip(sorted(remaining - {p1, p2}), range(2, 2 * r)):
                f[a] = b
            f[l1], f[l2] = y1, y2
            verify_map(T, G, f)
            COUNTS['clique_boundary_embeddings'] += 1
        print(f'boundary r={r}: {len(trees)} target trees, all exact maps verified', flush=True)


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, int(n ** .5) + 1))


def audit_unbounded_family():
    for r in range(2, 11):
        k = 2 * r + 1
        n = r * k + 1
        while not is_prime(n):
            n += 1
        cycles = []
        for j in range(1, r + 1):
            F = {edge(x, (x + j) % n) for x in range(n)}
            G = graph(n, F)
            assert nx.is_connected(G) and len(F) == n
            assert all(d == 2 for _, d in G.degree())
            cycles.append(F)
        E = set().union(*cycles)
        assert len(E) == r * n
        deleted = {edge(2*j, 2*j+1) for j in range(r-1)}
        C = graph(n, E - deleted)
        assert C.number_of_edges() == r * (n - 1) + 1
        assert min(dict(C.degree()).values()) == 2*r-1
        assert max(dict(C.degree()).values()) == 2*r
        for size in [2*r, k]:
            samples = [set(range(size)), {x % n for x in range(n-size, n)}]
            samples += [set(RNG.sample(range(n), size)) for _ in range(70)]
            for S in samples:
                ordered = sorted(S)
                gaps = [(ordered[(i+1) % size] - ordered[i]) % n for i in range(size)]
                assert max(gaps) >= r + 1
                eS = C.subgraph(S).number_of_edges()
                bound = r*size-r*(r+1)//2
                assert eS <= bound
                if size == k:
                    assert r*(size-1)-eS >= r*(r-1)//2
                else:
                    assert eS < size*(size-1)//2
                    if r >= 3:
                        assert r*(size-1)-eS >= 2*r-3
                COUNTS['cyclic_family_small_set_checks'] += 1
        COUNTS['cyclic_family_instances'] += 1
    print('unbounded-family construction audited at r=2,...,10', flush=True)


def main():
    started = time.monotonic()
    assert sha256((HERE / 'Spec.lean').read_bytes()).hexdigest() == SPEC_SHA
    for r in range(2, 5):
        for j in range(18):
            n = 2*r+1+j % 4
            C, B, f = extracted_circuit(r, n)
            ec = check_circuit(C, r)
            audit_tight_sets(C, r, ec)
            audit_components(C, r, B, f, ec)
            D, colors = frozen_exchange(C, B)
            # Every possible destination edge, not sampled destinations.
            for g in sorted(edges(C)):
                new_B = move_hole(C, B, f, g, D, colors)
                if g == sorted(edges(C))[0]:
                    audit_components(C, r, new_B, g, ec)
        print(f'circuit/exchange audits r={r}: done', flush=True)
    audit_boundary_and_clique()
    audit_unbounded_family()
    assert sha256((HERE / 'Spec.lean').read_bytes()).hexdigest() == SPEC_SHA
    print('COUNTS', dict(sorted(COUNTS.items())), flush=True)
    print('Spec SHA-256:', SPEC_SHA, flush=True)
    print(f'PASS in {time.monotonic()-started:.3f}s; no universal embedding conclusion inferred.', flush=True)


if __name__ == '__main__':
    main()
