#!/usr/bin/env python3
"""Exact checks for ResearchLightElimination.md. NOT a proof of W(c).

No previous Submission file is modified or imported. All optimization and
weight comparisons use exact integers or fractions. NetworkX is used for
graph storage and connectivity, not for a numerical optimization oracle.
"""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from pathlib import Path
import hashlib
import json
import random

import networkx as nx

SPEC_SHA256 = "429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde"


def edge(u, v):
    assert u != v
    return tuple(sorted((u, v)))


def cycle_edges(C):
    return [edge(C[i], C[(i + 1) % len(C)]) for i in range(len(C))]


def weight(C, lam):
    return sum((lam[v] for v in C), F())


def graph_of(D):
    G = nx.Graph()
    seen = set()
    for C in D:
        assert len(C) >= 3 and len(C) == len(set(C))
        ec = set(cycle_edges(C))
        assert not (seen & ec)
        seen |= ec
        G.add_edges_from(ec)
    assert all(d % 2 == 0 for _, d in G.degree())
    return G


def verify(G, D, lam):
    used = Counter()
    for C in D:
        assert len(C) >= 3 and len(C) == len(set(C)), C
        used.update(cycle_edges(C))
    assert used == Counter({edge(u, v): 1 for u, v in G.edges()})
    profile = tuple(sorted(weight(C, lam) for C in D))
    assert sum(profile, F()) == sum((F(d, 2) * lam[v]
                                    for v, d in G.degree()), F())
    return profile


def cycles(G):
    for root in sorted(G):
        def dfs(path, seen):
            v = path[-1]
            if len(path) >= 3 and root in G[v] and path[1] < v:
                yield tuple(path)
            for u in sorted(G[v]):
                if u > root and u not in seen:
                    yield from dfs(path + [u], seen | {u})
        yield from dfs([root], {root})


def exact(G, lam):
    """Full fair profile over ALL partitions; also counts all partitions."""
    E = sorted(edge(u, v) for u, v in G.edges())
    ei = {e: i for i, e in enumerate(E)}
    cc = list(cycles(G))
    masks = [sum(1 << ei[e] for e in cycle_edges(C)) for C in cc]
    ww = [weight(C, lam) for C in cc]
    byedge = [[] for _ in E]
    for j, mask in enumerate(masks):
        for i in range(len(E)):
            if mask >> i & 1:
                byedge[i].append(j)

    @lru_cache(None)
    def go(mask):
        if not mask:
            return (), (), 1
        i = (mask & -mask).bit_length() - 1
        best = None
        count = 0
        for j in byedge[i]:
            if masks[j] & mask != masks[j]:
                continue
            sub = go(mask ^ masks[j])
            if sub is None:
                continue
            count += sub[2]
            prof = tuple(sorted(sub[0] + (ww[j],)))
            if best is None or prof > best[0]:
                best = prof, (j,) + sub[1]
        if best is None:
            return None
        return best[0], best[1], count

    ans = go((1 << len(E)) - 1)
    assert ans is not None
    DD = tuple(cc[j] for j in ans[1])
    assert verify(G, DD, lam) == ans[0]
    return ans[0], DD, ans[2], len(cc), go.cache_info().currsize


def all_partitions(G):
    E = sorted(edge(u, v) for u, v in G.edges())
    ei = {e: i for i, e in enumerate(E)}
    cc = list(cycles(G))
    masks = [sum(1 << ei[e] for e in cycle_edges(C)) for C in cc]
    byedge = [[] for _ in E]
    for j, mask in enumerate(masks):
        for i in range(len(E)):
            if mask >> i & 1:
                byedge[i].append(j)

    def go(mask, used):
        if not mask:
            yield tuple(cc[j] for j in used)
            return
        i = (mask & -mask).bit_length() - 1
        for j in byedge[i]:
            if masks[j] & mask == masks[j]:
                yield from go(mask ^ masks[j], used + (j,))
    return go((1 << len(E)) - 1, ())


def chain_cycle(paths):
    """Concatenate compatible oriented paths to a simple closed word."""
    out = list(paths[0])
    for P in paths[1:]:
        assert out[-1] == P[0]
        out.extend(P[1:])
    assert out[0] == out[-1]
    C = tuple(out[:-1])
    assert len(C) >= 3 and len(C) == len(set(C))
    return C


def fan_partition(S, center, a=0, b=1):
    assert center in S and len(S) % 2 == 1
    rest = [v for v in S if v != center]
    return [(a, b, center)] + [(a, rest[i], b, rest[i + 1])
                              for i in range(0, len(rest), 2)]


def make_fan_repair(S, E, lam, x, y, z, a=0, b=1):
    """Re-pair the WHOLE fan, then absorb E at two or three contacts."""
    assert {x, y, z} <= set(S) and len({x, y, z}) == 3
    assert a not in E and b not in E and x in E and y in E
    other = [v for v in S if v not in (x, y, z)]
    fixed = [(a, other[i], b, other[i + 1])
             for i in range(0, len(other), 2)]
    old = [(a, b, z), (a, x, b, y), tuple(E)] + fixed
    j = E.index(x)
    E = tuple(E[j:]) + tuple(E[:j])
    if z not in E:
        j = E.index(y)
        R = E[:j + 1]
        T = E[j:] + (x,)
        Q = [chain_cycle([(a, b, x), R, (y, a)]),
             chain_cycle([(a, z, b, y), T, (x, a)])]
    else:
        if E.index(z) < E.index(y):
            y, z = z, y
            # The fan edge set is unchanged; use the corresponding pairing.
            old = [(a, b, z), (a, x, b, y), tuple(E)] + fixed
        i, j = E.index(y), E.index(z)
        R, T, U = E[:i + 1], E[i:j + 1], E[j:] + (x,)
        Q = [chain_cycle([(a, b, x), R, T, (z, a)]),
             chain_cycle([(a, x), tuple(reversed(U)), (z, b, y, a)])]
    G = graph_of(old)
    pold = verify(G, old, lam)
    new = Q + fixed
    pnew = verify(G, new, lam)
    m = lam[a] + lam[b] + lam[x]
    assert min(weight(c, lam) for c in old) == m
    assert all(weight(c, lam) > m for c in Q)
    assert pnew > pold
    return G, old, new


def check_fans():
    rng = random.Random(40991)
    absorption = reparings = pivots = 0
    for r in range(1, 10):
        S = list(range(2, 2 * r + 3))
        for rep in range(20):
            t = F(rng.randint(1, 9), rng.randint(1, 13))
            lam = {0: F(rng.randint(1, 7), 11),
                   1: F(rng.randint(1, 7), 13)}
            lam.update({v: t for v in S})
            for center in S:
                p = fan_partition(S, center)
                G = graph_of(p)
                prof = verify(G, p, lam)
                assert prof == (lam[0] + lam[1] + t,) + (
                    lam[0] + lam[1] + 2 * t,) * r
                reparings += 1
            count = rng.choice(range(2, min(len(S), 7) + 1))
            contacts = rng.sample(S, count)
            E = []
            nxt = max(S) + 1
            for v in contacts:
                E.append(v)
                for _ in range(rng.randint(1, 4)):
                    E.append(nxt)
                    lam[nxt] = F(rng.randint(1, 9), 17)
                    nxt += 1
            m = lam[0] + lam[1] + t
            lam[max(S) + 1] += m  # E is certainly not below m.
            x, y = contacts[:2]
            z = contacts[2] if count >= 3 else next(v for v in S if v not in contacts)
            G, old, new = make_fan_repair(S, E, lam, x, y, z)
            # The initial pairing can be completely unrelated to the chosen contacts.
            perm = S[:]
            rng.shuffle(perm)
            orig = fan_partition(perm, perm[0]) + [tuple(E)]
            assert verify(G, orig, lam) == verify(G, old, lam)
            absorption += 1

        for x, y, z in [(S[0], S[1], S[2]), (S[-1], S[0], S[1])]:
            p, q = max(S) + 1, max(S) + 2
            rest = [v for v in S if v not in (x, y, z)]
            fixed = [(0, rest[i], 1, rest[i + 1]) for i in range(0, len(rest), 2)]
            old = [(0, 1, z), (0, x, 1, y), (0, p, x, q)] + fixed
            new = [(0, x, p), (0, 1, x, q), (0, z, 1, y)] + fixed
            G = graph_of(old)
            lam = {v: F(1, 2 * r + 4) for v in G}
            assert verify(G, old, lam) == verify(G, new, lam)
            pivots += 1
    return dict(absorptions=absorption, equal_profile_repairings=reparings,
                square_pivots=pivots)


def three_terminal(rr):
    ends = [(0, 1), (1, 2), (2, 0)]
    sides = []
    old = [(0, 1, 2)]
    nxt = 3
    for (u, v), r in zip(ends, rr):
        paths = [(u, v)]
        for _ in range(2 * r):
            paths.append((u, nxt, v))
            nxt += 1
        sides.append(paths)
        for i in range(r):
            old.append(chain_cycle([paths[2 * i + 1],
                                    tuple(reversed(paths[2 * i + 2]))]))
    G = graph_of(old)
    s, R = min(rr), sum(rr)
    if s == 0:
        return G, old, tuple([F(3)] + [F(4)] * R)
    q = 2 * s + 1
    selected, new = [], []
    for i, paths in enumerate(sides):
        slots = [None] * q
        slots[i] = paths[0]
        branches = iter(paths[1:q])
        for j in range(q):
            if slots[j] is None:
                slots[j] = next(branches)
        selected.append(slots)
        spare = paths[q:]
        assert len(spare) % 2 == 0
        for j in range(0, len(spare), 2):
            new.append(chain_cycle([spare[j], tuple(reversed(spare[j + 1]))]))
    for j in range(q):
        new.append(chain_cycle([selected[i][j] for i in range(3)]))
    expected = tuple([F(4)] * (R - 3 * s) + [F(5)] * 3 + [F(6)] * (2 * s - 2))
    return G, new, expected


def check_three_terminal():
    small = states = partitions = 0
    for rr in product(range(3), repeat=3):
        if sum(rr) > 5:
            continue
        G, D, expected = three_terminal(rr)
        lam = {v: F(1) for v in G}
        assert verify(G, D, lam) == expected
        prof, opt, npart, _, ns = exact(G, lam)
        assert prof == expected, (rr, prof, expected)
        # Independently check the path-count classification on every partition.
        for P in all_partitions(G):
            q = sum({0, 1, 2} <= set(C) for C in P)
            assert q % 2 == 1 and 1 <= q <= 2 * min(rr) + 1
            assert len(P) == sum(rr) + (3 - q) // 2
            assert all(len(set(C) & {0, 1, 2}) in (2, 3) for C in P)
            partitions += 1
        small += 1
        states += ns
    big = 0
    for rr in [(1, 1, 1), (3, 5, 7), (10, 10, 10), (0, 50, 100),
               (30, 50, 100), (100, 100, 100)]:
        G, D, expected = three_terminal(rr)
        assert verify(G, D, {v: F(1) for v in G}) == expected
        big += 1
    return dict(exact_profiles=small, all_partitions_classified=partitions,
                dp_states=states, larger_partition_certificates=big)


def four_contact(length1, length2):
    a, b, c, d, x, y = range(6)
    p = tuple([b] + list(range(6, 6 + length1 - 1)) + [d])
    nxt = 6 + length1 - 1
    q = tuple([c] + list(range(nxt, nxt + length2 - 1)) + [a])
    C = (a, x, b, c, y, d)
    D = chain_cycle([(a, b), p, (d, c), q])
    G = graph_of([C, D])
    return G, C, D, p, q


def check_four_contact():
    rng = random.Random(7675)
    rational = original = 0
    for _ in range(100):
        G, C, D, p, q = four_contact(rng.randint(2, 8), rng.randint(2, 8))
        lam = {v: F(rng.randint(1, 10), rng.randint(1, 13)) for v in G}
        m = weight(C, lam)
        lam[p[1]] += 2 * m
        lam[q[1]] += 2 * m
        M = weight(D, lam)
        prof, opt, count, nc, _ = exact(G, lam)
        assert prof == (m, M) and count == 9 and nc == 19
        assert {frozenset(cycle_edges(A)) for A in opt} == {
            frozenset(cycle_edges(C)), frozenset(cycle_edges(D))}
        found = 0
        for P in all_partitions(G):
            profile = verify(G, P, lam)
            if profile == (m, M):
                found += 1
            else:
                assert min(profile) < m
            if len(P) == 2:
                assert all(set(range(4)) <= set(A) for A in P)
            else:
                assert len(P) == 3
                assert any(set(A) in ({0, 1, 4}, {2, 3, 5}) for A in P)
        assert found == 1
        rational += 1
    for L in list(range(2, 21)) + [30, 50, 100]:
        G, C, D, _, _ = four_contact(L, L)
        lam = {v: F(1, G.degree(v)) for v in G}
        assert weight(C, lam) == 2 and weight(D, lam) == L
        prof, _, count, nc, _ = exact(G, lam)
        assert prof == (F(2), F(L)) and count == 9 and nc == 19
        assert nx.is_biconnected(G) and min(dict(G.degree()).values()) == 2
        original += 1
    return dict(rational_weighted_cases=rational, original_degree_cases=original,
                partitions_per_case=9, cycles_per_case=19)


def check_triangle_deletion():
    rng = random.Random(72372)
    gg = [nx.convert_node_labels_to_integers(G) for G in nx.graph_atlas_g()
          if len(G) >= 5 and all(d % 2 == 0 for _, d in G.degree())
          and nx.node_connectivity(G) >= 3]
    for n in [8, 9, 10, 12, 16, 20, 25, 30]:
        for rep in range(3):
            while True:
                G = nx.random_regular_graph(4, n, seed=rng.randrange(10**9))
                if nx.node_connectivity(G) >= 3:
                    break
            # Add unused triangles: parity and vertex-connectivity are preserved.
            for _ in range(n):
                candidates = [T for T in combinations(G, 3)
                              if all(not G.has_edge(*e) for e in combinations(T, 2))]
                if not candidates:
                    break
                T = rng.choice(candidates)
                G.add_edges_from(combinations(T, 2))
            assert all(d % 2 == 0 for _, d in G.degree())
            gg.append(G)
    triangles = separators = 0
    for G in gg:
        tris = [T for T in combinations(sorted(G), 3)
                if all(G.has_edge(*e) for e in combinations(T, 2))]
        if len(G) > 10:
            rng.shuffle(tris)
            tris = tris[:30]
        for T in tris:
            H = G.copy()
            H.remove_edges_from(combinations(T, 2))
            assert nx.is_biconnected(H)
            assert min(dict(H.degree()).values()) >= 2
            pairs = list(combinations(sorted(H), 2))
            if len(G) > 12:
                rng.shuffle(pairs)
                pairs = pairs[:80]
            for pair in pairs:
                K = H.copy()
                K.remove_nodes_from(pair)
                comps = list(nx.connected_components(K))
                if len(comps) < 2:
                    continue
                remain = set(T) - set(pair)
                assert all(A & remain for A in comps)
                assert len(set(T) & set(pair)) <= 1
                assert len(comps) <= len(remain)
                if len(set(T) & set(pair)) == 1:
                    assert len(comps) == 2
                    assert all(len(A & remain) == 1 for A in comps)
                separators += 1
            triangles += 1
    return dict(graphs=len(gg), triangle_deletions=triangles,
                actual_two_separators_checked=separators)


def check_fair_triangle_constraints(G, D, lam, homogeneous):
    tris = [C for C in D if len(C) == 3]
    I = nx.Graph()
    for j, C in enumerate(tris):
        for v in C:
            I.add_edge(('c', j), ('v', v))
    if len(I):
        assert nx.is_forest(I)
        nv = len(set().union(*(set(C) for C in tris)))
        assert 2 * len(tris) == nv - nx.number_connected_components(I)
    if not D:
        return 0, 0
    m = min(weight(C, lam) for C in D)
    fanchecks = externals = 0
    if homogeneous and tris:
        assert m == 3 * next(iter(lam.values()))
        for C in tris:
            for a, b in combinations(C, 2):
                c = next(v for v in C if v not in (a, b))
                FF = [A for A in D if A != C and a in A and b in A]
                S = {c}
                for A in FF:
                    assert len(A) == 4 and c not in A
                    new = set(A) - {a, b}
                    assert not (S & new)
                    S |= new
                    assert all(G.has_edge(a, x) and G.has_edge(b, x) for x in new)
                assert len(S) == 2 * len(FF) + 1
                assert not any(G.has_edge(x, y) for x, y in combinations(S, 2))
                for A in D:
                    if A == C or A in FF:
                        continue
                    assert len(S & set(A)) <= 1
                    if S & set(A) and (a in A or b in A):
                        assert len(A) == 4
                    externals += 1
                fanchecks += 1
            types = [any(A != C and a in A and b in A for A in D)
                     for a, b in combinations(C, 2)]
            assert not all(types)
    return fanchecks, externals


def check_atlas():
    cases = fanchecks = externals = states = triangles = 0
    triangle_count_optima = triangle_count_fans = 0
    for G0 in nx.graph_atlas_g():
        if any(d % 2 for _, d in G0.degree()):
            continue
        G = nx.convert_node_labels_to_integers(G0)
        for mode in ('unit', 'original'):
            lam = {v: F(1) if mode == 'unit' or not G.degree(v)
                   else F(1, G.degree(v)) for v in G}
            prof, D, _, _, ns = exact(G, lam)
            f, e = check_fair_triangle_constraints(G, D, lam, mode == 'unit')
            fanchecks += f
            externals += e
            states += ns
            triangles += sum(len(C) == 3 for C in D)
            cases += 1
            if mode == 'unit' and any(len(C) == 3 for C in D):
                tau = sum(len(C) == 3 for C in D)
                for P in all_partitions(G):
                    tp = sum(len(C) == 3 for C in P)
                    assert tp >= tau
                    if tp == tau:
                        f, _ = check_fair_triangle_constraints(G, P, lam, True)
                        triangle_count_optima += 1
                        triangle_count_fans += f
    return dict(exact_fair_instances=cases, triangles_in_optima=triangles,
                whole_fans_checked=fanchecks, external_cycle_checks=externals,
                dp_states=states, triangle_count_optima=triangle_count_optima,
                triangle_count_fans=triangle_count_fans)


def robust_terminals(H, S):
    if not nx.is_connected(H):
        return False
    for size in range(3):
        for X in combinations(H, size):
            J = H.copy()
            J.remove_nodes_from(X)
            if any(not (A & (set(S) - set(X)))
                   for A in nx.connected_components(J)):
                return False
    return True


def check_terminal_connectivity():
    # This checks the equivalence (5.9), NOT the unproved terminal-mixing assertion.
    rng = random.Random(821)
    yes = no = 0
    for n in range(4, 11):
        for _ in range(20):
            H = nx.gnp_random_graph(n, rng.choice([0.2, 0.35, 0.6, 0.85]),
                                    seed=rng.randrange(10**9))
            S = set(rng.sample(range(n), rng.choice([s for s in (3, 5, 7) if s <= n])))
            G = H.copy()
            a, b = n, n + 1
            G.add_edge(a, b)
            G.add_edges_from((p, v) for p in (a, b) for v in S)
            is3 = nx.node_connectivity(G) >= 3
            assert is3 == robust_terminals(H, S)
            yes += is3
            no += not is3
    return dict(three_connected_cases=yes, non_three_connected_controls=no)


def main():
    folder = Path(__file__).resolve().parent
    protected = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                 for p in folder.iterdir() if p.is_file()
                 and not p.name.startswith('ResearchLightElimination')}
    assert protected['Spec.lean'] == SPEC_SHA256
    results = {}
    for name, fun in [('fan_exchanges', check_fans),
                      ('three_terminal', check_three_terminal),
                      ('four_contact', check_four_contact),
                      ('triangle_deletion', check_triangle_deletion),
                      ('global_fair_atlas', check_atlas),
                      ('terminal_connectivity', check_terminal_connectivity)]:
        results[name] = fun()
        print(name + ': ' + json.dumps(results[name], sort_keys=True), flush=True)
    for name, h in protected.items():
        assert hashlib.sha256((folder / name).read_bytes()).hexdigest() == h
    results['protected_files_unchanged'] = len(protected)
    results['status'] = 'All exact checks passed; W(c) remains unresolved.'
    print(json.dumps(results, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
