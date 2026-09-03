#!/usr/bin/env python3
"""Exact finite checks for ResearchReservoirExtension.md.

No conjectural cycle bound, solver, floating-point arithmetic, random test,
or execution of an old project file is used. Only JSON is written to stdout.
"""
import sys
sys.dont_write_bytecode = True
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import permutations, product
from math import factorial
from pathlib import Path
import json
import networkx as nx

SPEC_HASH = '429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde'
NEW_FILES = {'ResearchReservoirExtension.md', 'ResearchReservoirExtension.py'}


def key(x):
    return repr(x)


def edge(x, y):
    assert x != y
    return tuple(sorted((x, y), key=key))


def edges(G):
    return frozenset(edge(x, y) for x, y in G.edges())


def pe(P):
    P = tuple(P)
    assert len(P) >= 2 and len(set(P)) == len(P), P
    return frozenset(edge(x, y) for x, y in zip(P, P[1:]))


def ce(C):
    C = tuple(C)
    assert len(C) >= 3 and len(set(C)) == len(C), C
    return frozenset(edge(x, y) for x, y in zip(C, C[1:] + C[:1]))


def graph(es=(), vs=()):
    G = nx.Graph()
    G.add_nodes_from(sorted(vs, key=key))
    G.add_edges_from(sorted(es, key=key))
    return G


def rank(G):
    return len(G) - nx.number_connected_components(G)


def beta(G):
    return G.number_of_edges() - rank(G)


def partition(G, cycles, paths=()):
    used = Counter(e for C in cycles for e in ce(C))
    for P in paths:
        used.update(pe(P))
    assert used == Counter({e: 1 for e in edges(G)})


def greedy_partition(G):
    assert all(d % 2 == 0 for _, d in G.degree())
    R = G.copy()
    out = []
    while R.number_of_edges():
        basis = nx.cycle_basis(R)
        assert basis
        C = tuple(basis[0])
        out.append(C)
        R.remove_edges_from(ce(C))
        assert all(d % 2 == 0 for _, d in R.degree())
    partition(G, out)
    assert len(out) <= beta(G)
    return out


def all_cycles(G):
    vs = sorted(G, key=key)
    idx = {v: i for i, v in enumerate(vs)}
    for start in vs:
        def dfs(P, seen):
            for v in sorted(G[P[-1]], key=key):
                if v == start:
                    if len(P) >= 3 and idx[P[1]] < idx[P[-1]]:
                        yield tuple(P)
                elif idx[v] > idx[start] and v not in seen:
                    yield from dfs(P + [v], seen | {v})
        yield from dfs([start], {start})


def minimum_partition_small(G):
    """Exhaustive exact cover by all simple cycles; only used on atlas graphs."""
    if not G.number_of_edges():
        return [], 0, 0
    Cs = list(all_cycles(G))
    es = sorted(edges(G), key=key)
    eidx = {e: i for i, e in enumerate(es)}
    masks = [sum(1 << eidx[e] for e in ce(C)) for C in Cs]
    by_edge = [[] for _ in es]
    for j, C in enumerate(Cs):
        for e in ce(C):
            by_edge[eidx[e]].append(j)
    for L in by_edge:
        L.sort(key=lambda j: (-len(Cs[j]), j))
    calls = 0

    @lru_cache(None)
    def search(mask, slots):
        nonlocal calls
        calls += 1
        if not mask:
            return ()
        if slots <= 0:
            return None
        deg = Counter()
        live = []
        for i, (x, y) in enumerate(es):
            if mask & (1 << i):
                live.append(i)
                deg[x] += 1
                deg[y] += 1
        if max(deg.values()) // 2 > slots:
            return None
        if len(live) > slots * len(deg):
            return None
        choices = None
        for i in live:
            avail = [j for j in by_edge[i] if masks[j] & mask == masks[j]]
            if not avail:
                return None
            if choices is None or len(avail) < len(choices):
                choices = avail
                if len(avail) == 1:
                    break
        for j in choices:
            suffix = search(mask ^ masks[j], slots - 1)
            if suffix is not None:
                return (j,) + suffix
        return None

    lower = max(dict(G.degree()).values()) // 2
    upper = len(greedy_partition(G))
    for k in range(lower, upper + 1):
        answer = search((1 << len(es)) - 1, k)
        if answer is not None:
            D = [Cs[j] for j in answer]
            partition(G, D)
            assert len(D) == k
            return D, len(Cs), calls
    raise AssertionError('an even graph had no cycle partition')


def even_bipartite(X, Y):
    X, Y = list(X), list(Y)
    assert X and Y and len(X) % 2 == len(Y) % 2 == 0
    assert len(set(X + Y)) == len(X) + len(Y)
    if len(X) > len(Y):
        X, Y = Y, X
    p, z = len(X) // 2, len(Y) // 2
    X0, X1, Y0, Y1 = X[:p], X[p:], Y[:z], Y[z:]
    D = [tuple(v for j in range(p) for v in
               (X0[j], Y0[(i + j) % z], X1[j], Y1[(i + j) % z]))
         for i in range(z)]
    partition(graph(product(X, Y)), D)
    assert len(D) == z and all(len(C) == 4 * p for C in D)
    return D


def reservoir_routes(U, W, M):
    U, W = list(U), list(W)
    root = ('temporary-reservoir-root',)
    assert root not in U + W
    assert len(U) % 2 == 1 and len(W) >= 2 and len(W) % 2 == 0
    assert Counter(v for pair in M for v in pair) == Counter(W)
    D = even_bipartite([root] + U, W)
    Q, extra = [], []
    for C in D:
        if root in C:
            j = C.index(root)
            Q.append(C[j + 1:] + C[:j])
        else:
            extra.append(C)
    assert len(Q) == len(M)
    relabel = {}
    for path, (x, y) in zip(Q, M):
        relabel[path[0]], relabel[path[-1]] = x, y
    assert set(relabel) == set(W) == set(relabel.values())
    Q = [tuple(relabel.get(v, v) for v in P) for P in Q]
    extra = [tuple(relabel.get(v, v) for v in C) for C in extra]
    b, a = len(M), (len(U) - 1) // 2
    t, delta = min(2 * a, 2 * b - 2), max(0, a + 1 - b)
    assert len(extra) == delta
    assert all((Q[i][0], Q[i][-1]) == M[i] for i in range(b))
    assert all(len(set(P[1:-1]) & set(W)) == t for P in Q)
    assert all(len(set(P[1:-1]) & set(U)) == t + 1 for P in Q)
    assert all(sum(w in P[1:-1] for P in Q) == t // 2 for w in W)
    partition(graph(product(U, W)), extra, Q)
    return Q, extra


def action(Q, extra, M, pi, flips):
    """One global relabeling; reindex by new matching pair, not old route."""
    b = len(M)
    assert sorted(pi) == list(range(b)) and len(flips) == b
    relabel = {M[k][e]: M[pi[k]][e ^ flips[k]]
               for k in range(b) for e in (0, 1)}
    out = [None] * b
    for j, P in enumerate(Q):
        T = tuple(relabel.get(v, v) for v in P)
        i = pi[j]
        if T[0] != M[i][0]:
            T = T[::-1]
        assert (T[0], T[-1]) == M[i]
        out[i] = T
    cycles = [tuple(relabel.get(v, v) for v in C) for C in extra]
    return out, cycles


def pair_matrix(paths, M):
    return [[len(set(P[1:-1]) & set(pair)) for pair in M] for P in paths]


def conditional_expectation(T, A, assigned):
    b = len(T)
    remaining = [i for i in range(b) if i not in assigned.values()]
    m = len(remaining)
    row = [sum(A[i][v] for v in remaining) for i in range(b)]
    col = [sum(A[u][i] for u in remaining) for i in range(b)]
    square = sum(A[u][v] for u in remaining for v in remaining if u != v)
    total = F(0)
    for j in range(b):
        for k in range(b):
            if not T[j][k]:
                continue
            assert j != k
            if j in assigned and k in assigned:
                value = F(A[assigned[j]][assigned[k]])
            elif j in assigned:
                assert m >= 1
                value = F(row[assigned[j]], m)
            elif k in assigned:
                assert m >= 1
                value = F(col[assigned[k]], m)
            else:
                assert m >= 2
                value = F(square, m * (m - 1))
            total += T[j][k] * value
    return total / 2


def derandomized_routes(P, U, W, M, Q, extra):
    b = len(M)
    real = [set(path[1:-1]) for path in P]
    t = min(len(U) - 1, len(W) - 2)
    L = sum(len(V & set(W)) for V in real)
    if b == 1:
        assert L == t == 0
        return Q, extra, {'L': 0, 'I': 0, 'mean': F(0), 'permutation': [0]}
    A, T = pair_matrix(P, M), pair_matrix(Q, M)
    assert all(A[i][i] == T[i][i] == 0 for i in range(b))
    assert sum(map(sum, A)) == L
    assert all(sum(row) == t for row in T)
    mean = F(t * L, 2 * b - 2)
    assigned = {}
    current = conditional_expectation(T, A, assigned)
    assert current == mean
    for j in range(b):
        candidates = []
        for i in range(b):
            if i not in assigned.values():
                candidates.append((conditional_expectation(T, A, {**assigned, j: i}), i))
        # Check the tower-property calculation exactly at every decision.
        assert sum((v for v, _ in candidates), F(0)) / len(candidates) == current
        value, i = min(candidates)
        assert value <= current
        assigned[j] = i
        current = value
    pi = [assigned[j] for j in range(b)]
    where = {M[k][e]: (k, e) for k in range(b) for e in (0, 1)}
    flips = []
    chosen_score = 0
    average_score = F(0)
    for k in range(b):
        costs = []
        for bit in (0, 1):
            cost = 0
            for j, path in enumerate(Q):
                for v in path[1:-1]:
                    if v in where and where[v][0] == k:
                        endpoint_bit = where[v][1]
                        cost += M[pi[k]][endpoint_bit ^ bit] in real[pi[j]]
            costs.append(cost)
        flips.append(0 if costs[0] <= costs[1] else 1)
        chosen_score += min(costs)
        average_score += F(sum(costs), 2)
    assert average_score == current
    QQ, EE = action(Q, extra, M, pi, flips)
    I = sum(len(real[i] & set(QQ[i][1:-1])) for i in range(b))
    assert I == chosen_score and I <= current <= mean
    assert I <= mean.numerator // mean.denominator
    partition(graph(product(U, W)), EE, QQ)
    return QQ, EE, {'L': L, 'I': I, 'mean': mean, 'permutation': pi}


def path_extension(P, U, W):
    b, a = len(W) // 2, (len(U) - 1) // 2
    assert len(P) == b and not (set(U) & set().union(*(set(x) for x in P)))
    M = [(x[0], x[-1]) for x in P]
    assert Counter(v for pair in M for v in pair) == Counter(W)
    H = graph(set().union(*(pe(x) for x in P)))
    partition(H, [], P)
    Q, extra = reservoir_routes(U, W, M)
    Q, extra, info = derandomized_routes(P, U, W, M, Q, extra)
    out = list(extra)
    nullities = []
    for p, route in zip(P, Q):
        I = len(set(p[1:-1]) & set(route[1:-1]))
        assert not (pe(p) & pe(route))
        assert len(set(p) & set(route)) == 2 + I
        piece = graph(pe(p) | pe(route))
        assert nx.is_connected(piece) and all(d % 2 == 0 for _, d in piece.degree())
        assert beta(piece) == 1 + I
        part = greedy_partition(piece)
        assert len(part) <= 1 + I
        out.extend(part)
        nullities.append(1 + I)
    R = H.copy()
    R.add_edges_from(product(U, W))
    partition(R, out)
    delta = max(0, a + 1 - b)
    bound = b + delta + info['mean'].numerator // info['mean'].denominator
    assert len(out) <= bound
    if b == 1:
        assert len(out) == a + 1 == max(dict(R.degree()).values()) // 2
    info.update({'bound': bound, 'nullities': nullities})
    return R, out, info


def profile_price(b, s, D):
    assert b >= 1 and s >= 3 and s % 2
    a = (s - 1) // 2
    assert 0 <= D <= 2 * b * (b - 1)
    if b == 1:
        return a
    delta, k = max(0, a + 1 - b), min(a, b - 1)
    return min(max(a, b), delta + k * D // (b - 1))


def expand_partition(J, D, root, s, tag):
    partition(J, D)
    assert J.degree(root) > 0 and all(d % 2 == 0 for _, d in J.degree())
    W = sorted(J[root], key=key)
    b, a, q = len(W) // 2, (s - 1) // 2, s - 1
    H = J.copy()
    H.remove_node(root)
    P, retained = [], []
    for C in D:
        if root in C:
            k = C.index(root)
            P.append(C[k + 1:] + C[:k])
        else:
            retained.append(C)
    assert len(P) == b
    partition(H, retained, P)
    h, ell, z = {}, {}, {}
    for w in W:
        assert H.degree(w) % 2 == 1
        h[w] = (H.degree(w) - 1) // 2
        ell[w] = sum(w in path[1:-1] for path in P)
        z[w] = sum(w in C for C in retained)
        assert ell[w] + z[w] == h[w]
        assert ell[w] <= min(h[w], b - 1)
    L, capped = sum(ell.values()), sum(min(v, b - 1) for v in h.values())
    U = [(tag, 'new-twin', i) for i in range(s)]
    assert not set(U) & set(H)
    _, routed, info = path_extension(P, U, W)
    assert info['L'] == L
    R = H.copy()
    R.add_edges_from(product(U, W))
    collision_part = list(retained) + routed
    partition(R, collision_part)
    free_part = [tuple(U[0] if v == root else v for v in C) for C in D]
    free_part += even_bipartite(U[1:], W)
    partition(R, free_part)
    assert len(free_part) == len(D) + max(a, b)
    output = min((collision_part, free_part), key=len)
    B = profile_price(b, s, capped)
    assert len(output) <= len(D) + B
    specific = a if b == 1 else min(max(a, b), max(0, a + 1 - b) + min(a, b - 1) * L // (b - 1))
    assert len(output) <= len(D) + specific
    assert rank(R) - rank(J) == q
    assert nx.number_connected_components(R) == nx.number_connected_components(J)
    average_three = sum(H.degree(w) for w in W) <= 6 * b
    if average_three:
        assert L <= capped <= 2 * b
        assert B <= q + int(b == s and capped == 2 * b)
        assert 2 * B <= 3 * q
        assert B <= 2 * q
        if b >= s + 1:
            assert B <= q
    info.update({'U': U, 'W': W, 'H': H, 'b': b, 'D': capped, 'B': B,
                 'specific_price': specific, 'average_three': average_three,
                 'collision_count': len(collision_part), 'free_count': len(free_part)})
    return R, output, info


def matching_generator(W):
    if not W:
        yield []
        return
    x = W[0]
    for k in range(1, len(W)):
        for M in matching_generator(W[1:k] + W[k + 1:]):
            yield [(x, W[k])] + M


def real_paths(W, visits, tag, shared=True):
    """Arbitrary internal W orders; private links guarantee edge-disjointness.
    Every path also passes through the same nonterminal when shared=True.
    """
    b = len(W) // 2
    assert len(visits) == b
    P = []
    for i in range(b):
        sequence = [W[2 * i]] + [W[j] for j in visits[i]] + [W[2 * i + 1]]
        assert len(set(sequence)) == len(sequence)
        path = [sequence[0]]
        for j, end in enumerate(sequence[1:]):
            path.append((tag, 'private', i, j, 0))
            if shared and j == 0:
                path.extend([(tag, 'shared-hub'), (tag, 'private', i, j, 1)])
            path.append(end)
        P.append(tuple(path))
    return P


def check_factorizations_and_matchings():
    factor = route_grid = exhaustive = 0
    for p in range(1, 13):
        for z in range(1, 13):
            even_bipartite([('x', i) for i in range(2 * p)], [('y', i) for i in range(2 * z)])
            factor += 1
    for b in range(1, 17):
        W = [('w', i) for i in range(2 * b)]
        M = list(zip(W[::-1][::2], W[::-1][1::2]))
        for s in range(1, 32, 2):
            reservoir_routes([('u', i) for i in range(s)], W, M)
            route_grid += 1
    for b in range(1, 5):
        W = [('w', i) for i in range(2 * b)]
        for M in matching_generator(W):
            for s in (1, 3, 5, 9, 13):
                reservoir_routes([('u', i) for i in range(s)], W, M)
                exhaustive += 1
    return {'factorizations_p_z_1_to_12': factor,
            'routing_b_1_to_16_s_odd_1_to_31': route_grid,
            'all_matchings_through_8_terminals_five_sizes': exhaustive}


def check_global_group():
    outcomes = marginals = constant_outcomes = 0
    dependence = None
    for b in range(2, 6):
        W = [('gw', i) for i in range(2 * b)]
        M = list(zip(W[::2], W[1::2]))
        for s in (3, 5, 9):
            U = [('gu', i) for i in range(s)]
            Q, extra = reservoir_routes(U, W, M)
            G = graph(product(U, W))
            t = min(s - 1, 2 * b - 2)
            count = Counter()
            joint = total_I = local = 0
            P = real_paths(W, [[2 * ((i + 1) % b), 2 * ((i + 1) % b) + 1]
                               for i in range(b)], ('group-paths', b, s))
            for pi in permutations(range(b)):
                for flips in product((0, 1), repeat=b):
                    QQ, EE = action(Q, extra, M, pi, flips)
                    partition(G, EE, QQ)
                    for i, path in enumerate(QQ):
                        for w in set(path[1:-1]) & set(W):
                            assert w not in M[i]
                            count[i, w] += 1
                    I = sum(len(set(P[i][1:-1]) & set(QQ[i][1:-1])) for i in range(b))
                    total_I += I
                    if b == s:
                        assert I == b
                        constant_outcomes += 1
                    if b == s == 3:
                        joint += W[0] in QQ[1][1:-1] and W[0] in QQ[2][1:-1]
                    local += 1
            assert local == factorial(b) * 2 ** b
            for i in range(b):
                for w in W:
                    if w not in M[i]:
                        assert F(count[i, w], local) == F(t, 2 * b - 2)
                        marginals += 1
            assert F(total_I, local) == F(t * 2 * b, 2 * b - 2)
            if b == s == 3:
                assert joint == 0 and count[1, W[0]] == count[2, W[0]] == local // 2
                dependence = {'single_marginals': '1/2', 'joint_probability': '0'}
            outcomes += local
    return {'global_exact_partitions': outcomes, 'exact_marginal_equalities': marginals,
            'constant_collision_outcomes': constant_outcomes,
            'nonindependence_certificate': dependence}


def check_path_systems():
    cases = cap_minima = actual_collisions = saturated_averages = 0
    max_L = max_b = 0
    for b in list(range(1, 11)) + [12, 16]:
        W = [('pw', b, i) for i in range(2 * b)]
        patterns = [('empty', [[] for _ in range(b)])]
        if b >= 2:
            full = [[j for j in range(2 * b) if j // 2 != i] for i in range(b)]
            for i in range(b):
                full[i] = full[i][i % len(full[i]):] + full[i][:i % len(full[i])]
                if i % 2:
                    full[i].reverse()
            cyclic = [[2 * ((i + 1) % b), 2 * ((i + 1) % b) + 1] for i in range(b)]
            skew = [[] for _ in range(b)]
            budget = 2 * b
            for w in range(2 * b):
                for i in range(b):
                    if i != w // 2 and budget:
                        skew[i].append(w)
                        budget -= 1
            assert budget == 0
            patterns += [('full', full), ('cyclic-pair', cyclic), ('skew-average', skew)]
        for name, visits in patterns:
            P = real_paths(W, visits, ('path-case', b, name), shared=True)
            root = ('path-root', b, name)
            D = [(root,) + path for path in P]
            J = graph(set().union(*(ce(C) for C in D)), [('isolated-path-case', b, name)])
            partition(J, D)
            assert J.degree(root) // 2 == len(D) == b  # a minimum cap partition
            cap_minima += 1
            for s in (3, 5, 7, 11, 17, 33):
                R, DD, info = expand_partition(J, D, root, s, ('paths-expand', b, name, s))
                partition(R, DD)
                actual_collisions += info['I'] > 0
                saturated_averages += info['L'] == 2 * b
                max_L, max_b = max(max_L, info['L']), max(max_b, b)
                cases += 1
    # Unsubdivided real W-W edges must also be permitted.
    for b in range(1, 9):
        W = [('direct-w', b, i) for i in range(2 * b)]
        P = list(zip(W[::2], W[1::2]))
        for s in (3, 5, 9):
            _, _, info = path_extension(P, [('direct-u', i) for i in range(s)], W)
            assert info['L'] == info['I'] == 0
            cases += 1
    return {'lift_cases': cases, 'certified_minimum_caps': cap_minima,
            'positive_collision_cases': actual_collisions,
            'L_equals_2b_cases': saturated_averages, 'max_b': max_b, 'max_L': max_L}


def check_atlas():
    graphs = roots = expansions = avg = cycle_total = search_states = 0
    for index, J in enumerate(nx.graph_atlas_g()):
        if not J.number_of_edges() or any(d % 2 for _, d in J.degree()):
            continue
        graphs += 1
        D, nc, states = minimum_partition_small(J)
        cycle_total += nc
        search_states += states
        for root in sorted(J, key=key):
            if not J.degree(root):
                continue
            roots += 1
            for s in (3, 5, 7, 11):
                R, DD, info = expand_partition(J, D, root, s, ('atlas', index, root, s))
                partition(R, DD)
                expansions += 1
                avg += info['average_three']
    assert graphs == 77 and roots == 465
    return {'even_graphs_with_edges_through_order_7': graphs,
            'exact_minimum_cap_partitions': graphs, 'all_cycles_enumerated': cycle_total,
            'exact_cover_search_states': search_states, 'marked_nonisolated_roots': roots,
            'expansions': expansions, 'average_three_expansions': avg}


def check_prices():
    average_cases = general_cases = profiles = 0
    for b in range(1, 101):
        for a in range(1, 101):
            s, q = 2 * a + 1, 2 * a
            for D in range(min(2 * b, 2 * b * (b - 1)) + 1):
                B = profile_price(b, s, D)
                assert B <= q + int(b == s and D == 2 * b)
                assert 2 * B <= 3 * q and B <= 2 * q
                if b >= s + 1:
                    assert B <= q
                average_cases += 1
            values = {0, 1, b - 1, 2 * b - 2, 2 * b - 1, 2 * b,
                      2 * b + 1, b * (b - 1), 2 * b * (b - 1)}
            for D in sorted(v for v in values if 0 <= v <= 2 * b * (b - 1)):
                B = profile_price(b, s, D)
                assert B <= max(a, q * D // (2 * b) + 1)
                if b >= 2:
                    for twice_C in (1, 2, 3, 4, 5, 8):
                        if D <= twice_C * (b - 1) or 2 * b <= twice_C * q:
                            assert 2 * B <= twice_C * q
                general_cases += 1
    for b in range(1, 5):
        for h in product(range(b), repeat=2 * b):
            D = sum(h)
            for a in (1, 2, 3, 5):
                B = profile_price(b, 2 * a + 1, D)
                if D <= 2 * b:
                    assert B <= 2 * a + int(b == 2 * a + 1 and D == 2 * b)
            profiles += 1
    return {'average_three_integer_cases_b_a_1_to_100': average_cases,
            'general_profile_price_cases': general_cases,
            'all_capped_profiles_b_1_to_4': profiles}


def check_unbalanced():
    checks = max_degree = 0
    for b in range(1, 11):
        W = [('uw', b, i) for i in range(2 * b)]
        root = ('unbalanced-root', b)
        D = [(root, W[2 * i], W[2 * i + 1]) for i in range(b)]
        D += [(W[0], ('petal', b, j, 0), ('petal', b, j, 1)) for j in range(2 * b)]
        J = graph(set().union(*(ce(C) for C in D)))
        assert len(D) == beta(J) == 3 * b
        assert all(max(dict(J.subgraph(vs).degree()).values()) == 2
                   for vs in nx.biconnected_components(J))
        for s in (3, 5, 9, 17):
            R, DD, info = expand_partition(J, D, root, s, ('unbalanced-expand', b, s))
            H = info['H']
            assert sum(H.degree(w) for w in W) == 6 * b
            assert H.degree(W[0]) == 4 * b + 1
            assert info['L'] == 0 and info['D'] == b - 1
            assert len(DD) == 3 * b + max(0, (s + 1) // 2 - b)
            max_degree = max(max_degree, H.degree(W[0]))
            checks += 1
    return {'expansions': checks, 'largest_external_terminal_degree': max_degree,
            'external_average_in_every_case': 3}


def check_constant_template_and_alternative():
    sizes = []
    for b in range(3, 18, 2):
        W = [('cw', b, i) for i in range(2 * b)]
        U = [('cu', b, i) for i in range(b)]
        M = list(zip(W[::2], W[1::2]))
        Q, extra = reservoir_routes(U, W, M)
        T = pair_matrix(Q, M)
        assert not extra and all(T[j][k] == int(j != k) for j in range(b) for k in range(b))
        P = real_paths(W, [[2 * ((i + 1) % b), 2 * ((i + 1) % b) + 1]
                           for i in range(b)], ('constant-paths', b))
        R, D, info = path_extension(P, U, W)
        assert info['I'] == info['mean'] == b
        assert len(D) == 2 * b
        sizes.append(b)
        if b == 3:
            alternative = []
            for i in range(b):
                k = (i - 1) % b
                alternative.append((M[i][0], U[0], M[k][1], U[1], M[k][0], U[2], M[i][1]))
            partition(graph(product(U, W)), [], alternative)
            combined = []
            for p, route in zip(P, alternative):
                assert set(p) & set(route) == {p[0], p[-1]}
                combined.append(p + tuple(reversed(route[1:-1])))
            partition(R, combined)
            assert len(combined) == max(dict(R.degree()).values()) // 2 == 3
    return {'constant_template_sizes': sizes, 'b_s_3_fixed_template_cycles': 6,
            'b_s_3_alternative_optimal_cycles': 3}


def check_repeated_ledger():
    D = [(('triangle', j, 0), ('triangle', j, 1), ('triangle', j, 2)) for j in range(3)]
    K = graph(set().union(*(ce(C) for C in D)), [('ledger-isolate',)])
    initial_count, initial_rank = len(D), rank(K)
    current = K
    history = []
    for j in range(3):
        for k, s in ((0, 3), (1, 5)):
            root = ('triangle', j, k)
            old = current.copy()
            current, D, info = expand_partition(current, D, root, s, ('ledger', j, k))
            assert info['average_three']
            history.append((old, root, s, info))
    partition(current, D)
    final = current.copy()
    total_q = total_B = 0
    for old, root, s, info in reversed(history):
        U, W = info['U'], info['W']
        assert all(set(current[u]) == set(W) for u in U)
        assert not any(current.has_edge(x, y) for x in U for y in U if x != y)
        smaller = current.copy()
        smaller.remove_nodes_from(U)
        assert sum(smaller.degree(w) for w in W) <= 3 * len(W)
        smaller.add_edges_from((root, w) for w in W)
        assert set(smaller) == set(old) and edges(smaller) == edges(old)
        assert rank(current) - rank(smaller) == s - 1
        total_q += s - 1
        total_B += info['B']
        current = smaller
    assert set(current) == set(K) and edges(current) == edges(K)
    assert rank(final) - initial_rank == total_q
    assert len(D) <= initial_count + total_B and 2 * total_B <= 3 * total_q
    return {'contractions': len(history), 'deleted_rank': total_q,
            'sum_profile_prices': total_B, 'core_cycles': initial_count,
            'lifted_cycles': len(D), 'unchanged_component_count': nx.number_connected_components(K)}


def check_near_twins():
    cases = 0
    max_error = 0
    merge_counts = Counter()
    for b in range(1, 9):
        W = [('nw', b, i) for i in range(2 * b)]
        Z = [('nz', b, j) for j in range(2)]
        root = ('near-root', b)
        for mode, expected_merges in (('attached', 0), ('separate-cycle', 1), ('isolated', 2)):
            D = [(root, W[2 * i], W[2 * i + 1]) for i in range(b)]
            if mode == 'attached':
                D.append((W[0], Z[0], Z[1]))
            elif mode == 'separate-cycle':
                D.append((('third-z', b), Z[0], Z[1]))
            J = graph(set().union(*(ce(C) for C in D)), Z + [('near-isolate', b)])
            for s in (3, 5, 7, 11, 17):
                R, RD, info = expand_partition(J, D, root, s, ('near', b, s, mode))
                U = info['U']
                err = graph(product(U[:-1], Z), R.nodes())
                assert all(d % 2 == 0 for _, d in err.degree())
                assert not edges(R) & edges(err)
                FD = even_bipartite(U[:-1], Z)
                partition(err, FD)
                assert len(FD) <= min(err.number_of_edges() // 4, beta(err))
                G = R.copy()
                G.add_edges_from(edges(err))
                partition(G, RD + FD)
                q = s - 1
                assert err.number_of_edges() == 2 * q
                assert info['average_three']
                assert info['B'] + len(FD) <= 2 * q
                merges = nx.number_connected_components(J) - nx.number_connected_components(G)
                assert merges == expected_merges
                assert rank(G) - rank(J) == q + merges
                assert len(RD + FD) <= len(D) + 2 * (rank(G) - rank(J))
                max_error = max(max_error, err.number_of_edges())
                merge_counts[merges] += 1
                cases += 1
    return {'even_surplus_near_twin_cases': cases, 'largest_surplus_edge_count': max_error,
            'cases_by_component_merges': dict(sorted(merge_counts.items()))}


def chain_obstruction(h):
    V = [('junction', h, j) for j in range(h + 1)]
    W = [V[0], V[-1]]
    U = [('chain-u', h, i) for i in range(3)]
    branches = [[(V[j - 1], ('branch', h, j, k), V[j]) for k in range(3)]
                for j in range(1, h + 1)]
    H = graph(set().union(*(pe(P) for B in branches for P in B)))
    long = [tuple(v for j in range(h) for v in branches[j][k][:-1]) + (V[-1],)
            for k in range(3)]
    R = H.copy()
    R.add_edges_from(product(U, W))
    RD = [P + (U[k],) for k, P in enumerate(long)]
    partition(R, RD)
    assert len(RD) == max(dict(R.degree()).values()) // 2 == 3
    JD = [long[0] + (U[0],)]
    JD += [(V[j], ('branch', h, j + 1, 1), V[j + 1], ('branch', h, j + 1, 2))
           for j in range(h)]
    Fcycle = (W[0], U[1], W[1], U[2])
    deleted = R.copy()
    deleted.remove_edges_from(ce(Fcycle))
    partition(deleted, JD)
    assert len(JD) == h + 1 and len(ce(Fcycle)) == 4
    assert deleted.degree(U[1]) == deleted.degree(U[2]) == 0
    # Certify the block classification used by the paper lower bound.
    blocks = [H.subgraph(vs) for vs in nx.biconnected_components(H)]
    assert len(blocks) == h
    assert all(len(B) == 5 and sorted(d for _, d in B.degree()) == [2, 2, 2, 3, 3]
               and nx.is_bipartite(B) for B in blocks)
    assert all(H.degree(w) == 3 for w in W)
    return {'h': h, 'complete_reservoir_c': 3, 'after_four_edge_deletion_c': h + 1,
            'increase': h - 2}


def check_density():
    result = []
    for s in (5, 7, 11, 21, 51, 101):
        b = s
        U, W = [('du', i) for i in range(s)], [('dw', i) for i in range(2 * b)]
        R = graph(list(product(U[:-2], W[:-4])) + list(product(U[-2:-1], W[-4:-2]))
                  + list(product(U[-1:], W[-2:])))
        assert all(R.degree(u) > 0 and R.degree(u) % 2 == 0 for u in U)
        assert all(R.degree(w) % 2 == 1 for w in W)
        assert nx.number_connected_components(R) == 3
        assert not nx.has_path(R, W[0], W[-4])
        rest = [w for w in W if w not in (W[0], W[-4])]
        M = [(W[0], W[-4])] + list(zip(rest[::2], rest[1::2]))
        assert Counter(v for pair in M for v in pair) == Counter(W)
        density = F(R.number_of_edges(), 2 * b * s)
        assert density == 1 - F(4 * s + 4 * b - 12, 2 * b * s)
        result.append({'s': s, 'b': b, 'density': str(density), 'unroutable_prescribed_pair': True})
    # Dense even graphs need not have an independent triple.
    for n in range(3, 32, 2):
        G = nx.complete_graph(n)
        assert all(d % 2 == 0 for _, d in G.degree())
        assert nx.number_of_edges(nx.complement(G)) == 0
    return result


def main():
    directory = Path(__file__).resolve().parent
    protected = {p.name: sha256(p.read_bytes()).hexdigest()
                 for p in directory.iterdir() if p.is_file() and p.name not in NEW_FILES}
    assert protected['Spec.lean'] == SPEC_HASH
    result = {}
    result['factorizations_and_matchings'] = check_factorizations_and_matchings()
    result['global_randomization'] = check_global_group()
    result['shared_path_systems'] = check_path_systems()
    result['atlas'] = check_atlas()
    result['price_arithmetic'] = check_prices()
    result['unbalanced_degrees'] = check_unbalanced()
    result['template_limit_not_graph_obstruction'] = check_constant_template_and_alternative()
    result['repeated_rank_ledger'] = check_repeated_ledger()
    result['near_twins'] = check_near_twins()
    result['four_edge_deletion'] = [chain_obstruction(h) for h in list(range(1, 33)) + [64]]
    result['density_routing_obstruction'] = check_density()
    after = {p.name: sha256(p.read_bytes()).hexdigest()
             for p in directory.iterdir() if p.is_file() and p.name not in NEW_FILES}
    assert protected == after
    result['protected_file_count'] = len(protected)
    result['spec_sha256'] = SPEC_HASH
    result['status'] = 'all exact checks passed; no universal EG claim'
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
