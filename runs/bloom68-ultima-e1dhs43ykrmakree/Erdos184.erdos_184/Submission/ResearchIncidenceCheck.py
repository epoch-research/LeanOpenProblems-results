#!/usr/bin/env python3
"""Exact finite checks for ResearchIncidence.md (not a proof of Erdős--Gallai).

Requires Python 3 and NetworkX.  No LP, MILP, floating-point rank, or random
optimality claim is used.  All random tests use a fixed seed; the infinite
families and theorems are proved in the companion note.
"""
from collections import Counter, defaultdict
from functools import lru_cache
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
import hashlib
import json
import random

import networkx as nx

SPEC_SHA256 = "429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde"


def edge(u, v):
    assert u != v
    return (u, v) if u < v else (v, u)


def word_edges(word):
    assert word
    return [edge(word[i], word[(i + 1) % len(word)])
            for i in range(len(word))]


def partition_graph(cycles, nodes=None, target=None):
    used = set()
    G = nx.Graph()
    if nodes is not None:
        G.add_nodes_from(nodes)
    for C in cycles:
        assert len(C) >= 3 and len(set(C)) == len(C), C
        E = set(word_edges(C))
        assert len(E) == len(C) and not (used & E)
        used |= E
        G.add_edges_from(E)
    assert all(d % 2 == 0 for _, d in G.degree())
    if target is not None:
        assert used == {edge(u, v) for u, v in target}
    return G


def all_cycles(G):
    """One orientation/rotation of every simple undirected cycle."""
    for root in sorted(G):
        def dfs(path, seen):
            u = path[-1]
            if len(path) >= 3 and root in G[u] and path[1] < u:
                yield tuple(path)
            for v in sorted(G[u]):
                if v > root and v not in seen:
                    yield from dfs(path + [v], seen | {v})
        yield from dfs([root], {root})


def exact_optimum(G, forced_pair=None):
    """Exhaustive cycle exact cover, with exact degree/length lower bounds."""
    E = sorted(edge(u, v) for u, v in G.edges())
    if not E:
        assert forced_pair is None
        return (), 0
    index = {e: j for j, e in enumerate(E)}
    C = list(all_cycles(G))
    masks = [sum(1 << index[e] for e in word_edges(c)) for c in C]
    byedge = [[] for _ in E]
    for j, mask in enumerate(masks):
        for k in range(len(E)):
            if mask >> k & 1:
                byedge[k].append(j)
    for a in byedge:
        a.sort(key=lambda j: (-len(C[j]), C[j]))
    inc = {v: sum(1 << k for k, e in enumerate(E) if v in e) for v in G}

    @lru_cache(None)
    def solve(mask, budget):
        if not mask:
            return ()
        if budget <= 0:
            return None
        if max((mask & bits).bit_count() // 2 for bits in inc.values()) > budget:
            return None
        if mask.bit_count() > budget * len(G):
            return None
        choices = None
        for k in range(len(E)):
            if mask >> k & 1:
                a = [j for j in byedge[k] if masks[j] & mask == masks[j]]
                if not a:
                    return None
                if choices is None or len(a) < len(choices):
                    choices = a
        for j in choices:
            suffix = solve(mask ^ masks[j], budget - 1)
            if suffix is not None:
                return (j,) + suffix
        return None

    full = (1 << len(E)) - 1
    lb = max(d // 2 for _, d in G.degree())
    for k in range(lb, len(E) // 3 + 1):
        if forced_pair is None:
            ans = solve(full, k)
        else:
            ans = None
            for j, c in enumerate(C):
                if set(forced_pair) <= set(c):
                    suffix = solve(full ^ masks[j], k - 1)
                    if suffix is not None:
                        ans = (j,) + suffix
                        break
        if ans is not None:
            out = tuple(C[j] for j in ans)
            partition_graph(out, G.nodes(), G.edges())
            assert len(out) == k
            return out, len(C)
    raise AssertionError("even graph had no cycle partition")


def arcs(C, a, b):
    assert a != b and a in C and b in C
    i, j, L = C.index(a), C.index(b), len(C)
    out = []
    for step in (1, -1):
        P = [a]
        k = i
        while k != j:
            k = (k + step) % L
            P.append(C[k])
        out.append(P)
    return out


def split_word(word):
    """Split an edge-simple closed trail at repeated vertices."""
    todo = [list(word)]
    out = []
    while todo:
        W = todo.pop()
        first = {}
        for j, v in enumerate(W):
            if v in first:
                i = first[v]
                A, B = W[i:j], W[j:] + W[:i]
                assert len(A) >= 3 and len(B) >= 3
                todo.extend((A, B))
                break
            first[v] = j
        else:
            assert len(W) >= 3
            out.append(tuple(W))
    return out


def noncycle_blocks(G):
    count = 0
    for E in nx.biconnected_component_edges(G):
        H = nx.Graph()
        H.add_edges_from(E)
        assert all(d % 2 == 0 for _, d in H.degree())
        if not all(d == 2 for _, d in H.degree()):
            count += 1
    return count


def ring_data(cycles, connectors):
    s = len(cycles)
    assert s >= 3 and len(set(connectors)) == s
    A = [arcs(C, connectors[i - 1], connectors[i])
         for i, C in enumerate(cycles)]
    incidence = defaultdict(list)
    for i, C in enumerate(cycles):
        for v in C:
            incidence[v].append(i)
    branching = sum(max(0, len(I) - 2) for I in incidence.values())
    constraints = []
    for v, I in incidence.items():
        if v not in connectors and len(I) >= 2:
            literals = [(i, 0 if v in A[i][0] else 1) for i in I]
            constraints.append((v, literals))
    return A, incidence, branching, constraints


def evaluate_ring(cycles, connectors, bits):
    A, incidence, B, constraints = ring_data(cycles, connectors)
    words = [sum((A[i][bits[i] ^ j][:-1] for i in range(len(cycles))), [])
             for j in (0, 1)]
    violated = [v for v, L in constraints
                if len({bits[i] ^ a for i, a in L}) == 1]
    D = sum(len(W) - len(set(W)) for W in words)
    assert D == B + len(violated)
    target = set(e for C in cycles for e in word_edges(C))
    assert len(target) == sum(map(len, cycles))
    assert Counter(e for W in words for e in word_edges(W)) == Counter(target)
    out = split_word(words[0]) + split_word(words[1])
    partition_graph(out, target=target)
    eta = 0
    for W in words:
        R = nx.Graph()
        R.add_edges_from(word_edges(W))
        assert nx.is_connected(R)
        eta_R = noncycle_blocks(R)
        assert 2 * eta_R <= len(W) - len(set(W))
        eta += eta_R
    assert len(out) <= 2 + D - eta
    return B, len(violated), words, out, eta


def frustration(cycles, connectors):
    values = [evaluate_ring(cycles, connectors, bits)
              for bits in product((0, 1), repeat=len(cycles))]
    return min(v[1] for v in values), values


def make_ring(s, entries, rng, connector_chords=()):
    """Realize arbitrary signed NAE constraints; subdivide every segment."""
    connectors = list(range(s))
    interior = [[[], []] for _ in range(s)]
    fresh = s
    for I, signs in entries:
        v = fresh
        fresh += 1
        assert len(I) == len(set(I)) and len(I) == len(signs)
        for i, a in zip(I, signs):
            interior[i][a].append(v)
    for i, j, a in connector_chords:
        assert j not in (i - 1, i) and j % s not in ((i - 1) % s, i)
        interior[i][a].append(connectors[j])
    cycles = []
    for i in range(s):
        paths = []
        for a in (0, 1):
            rng.shuffle(interior[i][a])
            V = [connectors[i - 1]] + interior[i][a] + [connectors[i]]
            P = [V[0]]
            for v in V[1:]:
                P.extend((fresh, v))
                fresh += 1
            paths.append(P)
        cycles.append(tuple(paths[0] + list(reversed(paths[1][1:-1]))))
    partition_graph(cycles)
    return cycles, connectors


def weighted_balancing_check(cycles, connectors, rng):
    A, incidence, B, constraints = ring_data(cycles, connectors)
    if B:
        return False
    valid = [bits for bits in product((0, 1), repeat=len(cycles))
             if all(len({bits[i] ^ a for i, a in L}) == 2
                    for _, L in constraints)]
    if not valid:
        return False
    bits = list(valid[0])
    F = nx.Graph()
    F.add_nodes_from(range(len(cycles)))
    for _, L in constraints:
        assert len(L) == 2
        F.add_edge(L[0][0], L[1][0])
    weights = {e: Fraction(rng.randrange(1, 20), rng.randrange(1, 9))
               for C in cycles for e in word_edges(C)}
    def pathweight(P):
        return sum((weights[edge(u, v)] for u, v in zip(P, P[1:])), Fraction())
    balance = Fraction()
    largest = Fraction()
    largest_mass = Fraction()
    for block in nx.connected_components(F):
        d = sum((pathweight(A[i][bits[i]]) - pathweight(A[i][1 ^ bits[i]])
                 for i in block), Fraction())
        mass = sum((sum((weights[e] for e in word_edges(cycles[i])), Fraction())
                    for i in block), Fraction())
        largest = max(largest, abs(d))
        largest_mass = max(largest_mass, mass)
        if abs(balance + d) > abs(balance - d):
            for i in block:
                bits[i] ^= 1
            d = -d
        balance += d
    _, mu, words, _, _ = evaluate_ring(cycles, connectors, bits)
    assert mu == 0
    W = [sum((weights[e] for e in word_edges(T)), Fraction()) for T in words]
    assert abs(W[0] - W[1]) <= largest <= largest_mass
    assert min(W) >= (sum(W) - largest) / 2
    return True


def incidence_graph(sets, nodes):
    B = nx.Graph()
    B.add_nodes_from(("v", v) for v in nodes)
    for i, S in enumerate(sets):
        B.add_node(("p", i))
        B.add_edges_from((("p", i), ("v", v)) for v in S)
    return B


def chromatic_number(G):
    if not G:
        return 0
    order = sorted(G, key=lambda v: -G.degree(v))
    for k in range(1, len(G) + 1):
        col = {}
        def rec(t):
            if t == len(order):
                return True
            v = order[t]
            forbidden = {col[w] for w in G[v] if w in col}
            for c in range(k):
                if c not in forbidden:
                    col[v] = c
                    if rec(t + 1):
                        return True
            col.pop(v, None)
            return False
        if rec(0):
            return k
    raise AssertionError


def packet_check(G, cycles):
    groups = defaultdict(list)
    for C in cycles:
        groups[frozenset(C)].append(C)
    S, multiplicities = list(groups), [len(a) for a in groups.values()]
    Q = nx.Graph()
    Q.add_nodes_from(range(len(S)))
    Q.add_edges_from((i, j) for i, j in combinations(range(len(S)), 2)
                     if len(S[i] & S[j]) >= 2)
    rank = len(G) - nx.number_connected_components(G)
    independent_count = 0
    for mask in range(1 << len(S)):
        I = [i for i in Q if mask >> i & 1]
        if any(Q.has_edge(i, j) for i, j in combinations(I, 2)):
            continue
        B = incidence_graph([S[i] for i in I], G)
        assert nx.is_forest(B) if B else True
        assert sum(len(S[i]) - 1 for i in I) == len(G) - nx.number_connected_components(B)
        assert sum(len(S[i]) - 1 for i in I) <= rank
        assert 2 * sum(multiplicities[i] for i in I) <= rank
        independent_count += 1
    for s, k in zip(S, multiplicities):
        assert 2 * k <= len(s) - 1
    chi = chromatic_number(Q)
    assert 2 * len(cycles) <= chi * rank
    return independent_count


def walecki(vertices):
    """Hamilton partition of K_(2d+1), explicit and checked edgewise."""
    n = len(vertices)
    assert n % 2 == 1 and n >= 3
    d, M = (n - 1) // 2, n - 1
    out = []
    for t in range(d):
        order = [t]
        for j in range(1, d):
            order.extend(((t - j) % M, (t + j) % M))
        order.append((t - d) % M)
        out.append(tuple([vertices[-1]] + [vertices[i] for i in order]))
    partition_graph(out, target=combinations(vertices, 2))
    return out


def tripartite_hamilton(A, B, C):
    s = len(A)
    assert s == len(B) == len(C) and s % 2 == 1
    out = [tuple(v for i in range(s)
                 for v in (A[i], B[(i + t) % s], C[(i + 2 * t) % s]))
           for t in range(s)]
    target = [(u, v) for X, Y in ((A, B), (B, C), (C, A)) for u in X for v in Y]
    partition_graph(out, target=target)
    return out


def laminar_partition(h):
    n = 3 ** h
    out, packets = [], []
    def rec(V, depth):
        if len(V) == 1:
            return
        s = len(V) // 3
        parts = [V[j * s:(j + 1) * s] for j in range(3)]
        C = tripartite_hamilton(*parts)
        out.extend(C)
        packets.append((frozenset(V), depth, C))
        for W in parts:
            rec(W, depth + 1)
    rec(list(range(n)), 0)
    G = partition_graph(out, nodes=range(n), target=combinations(range(n), 2))
    assert len(out) == h * n // 3
    return G, out, packets


def binary_rank(sets):
    basis = {}
    for S in sets:
        x = sum(1 << v for v in S)
        while x:
            lead = x.bit_length() - 1
            if lead not in basis:
                basis[lead] = x
                break
            x ^= basis[lead]
    return len(basis)


def four_cycle_span_dimension(cycles):
    """Exact F_2 span of incidence squares, not vertex-incidence rank."""
    sets = [set(C) for C in cycles]
    E = {(i, v): k for k, (i, v) in enumerate(
        (i, v) for i, S in enumerate(sets) for v in sorted(S))}
    B = incidence_graph(sets, set().union(*sets))
    target = len(E) - len(B) + nx.number_connected_components(B)
    basis = {}
    for i, j in combinations(range(len(sets)), 2):
        for u, v in combinations(sorted(sets[i] & sets[j]), 2):
            x = sum(1 << E[e] for e in ((i, u), (j, u), (i, v), (j, v)))
            while x:
                p = x.bit_length() - 1
                if p not in basis:
                    basis[p] = x
                    break
                x ^= basis[p]
            if len(basis) == target:
                return target
    return len(basis)


def laminar_ring_checks(packets):
    root = next(P for S, depth, P in packets if depth == 0)
    leaves = [P[0] for S, depth, P in packets if len(S) == 3]
    if len(root) < 2:
        return 0
    L, M = leaves[:2]
    outside = next(v for v in root[0] if v not in L)
    instances = [([root[0], root[1], L], [outside, L[0], L[1]]),
                 ([root[0], L, root[1], M], [L[0], L[1], M[0], M[1]])]
    for D, x in instances:
        s = len(D)
        _, values = frustration(D, x)
        bysize = sorted(D, key=len, reverse=True)
        assert set(bysize[1]) <= set(bysize[0])
        assert all(set(C) <= set(bysize[1]) for C in bysize[2:])
        B = sum(map(len, bysize[2:]))
        assert B >= 3 * (s - 2)
        for branch, f, words, out, eta in values:
            assert branch == B
            # The proved upper-bound certificate is too large to help,
            # regardless of how few cycles an actual split might produce.
            assert 2 + B + f - eta > s
    return len(instances)


def replace_edges(C, replacements):
    """replacements are (u,v,interior_word), with either edge orientation."""
    lookup = {edge(u, v): (u, v, list(P)) for u, v, P in replacements}
    out, found = [], set()
    for u, v in zip(C, C[1:] + C[:1]):
        out.append(u)
        if edge(u, v) in lookup:
            a, b, P = lookup[edge(u, v)]
            out.extend(P if (u, v) == (a, b) else list(reversed(P)))
            found.add(edge(u, v))
    assert found == set(lookup)
    return tuple(out)


def same_incidence_pair(t):
    assert t >= 2
    R = (0, 1, 2, 3, 4)
    F = [(0, 2, 4, 1, 3)]
    H1, H2 = (0, 1, 3, 2, 4), (0, 2, 1, 4, 3)
    for k in range(1, t):
        V = list(range(5 * k, 5 * k + 5))
        E1, E2 = set(word_edges(H1)), set(word_edges(H2))
        directed_R = list(zip(R, R[1:] + R[:1]))
        u, v = next((u, v) for u, v in directed_R if edge(u, v) in E1)
        w, z = next((u, v) for u, v in directed_R if edge(u, v) in E2)
        R = replace_edges(R, [(u, v, [V[j] for j in (0, 2, 4)]),
                              (w, z, [V[j] for j in (1, 3)])])
        H1 = replace_edges(H1, [(u, v, [V[j] for j in (0, 1, 3, 2, 4)])])
        H2 = replace_edges(H2, [(w, z, [V[j] for j in (1, 2, 0, 4, 3)])])
        F.append(tuple(V))
        good = partition_graph(F + [R])
        partition_graph([H1, H2], target=good.edges())
    n = 5 * t
    good_D = F + [R]
    good = partition_graph(good_D, nodes=range(n))
    assert all(len(C) == n for C in (R, H1, H2))
    partition_graph([H1, H2], nodes=range(n), target=good.edges())
    paths = [tuple(C[j] for j in (0, 2, 4, 1, 3)) for C in F]
    R_bad = tuple(v for P in paths for v in P)
    bad_D = F + [R_bad]
    bad = partition_graph(bad_D, nodes=range(n))
    assert all(d == 4 for _, d in good.degree())
    assert all(d == 4 for _, d in bad.degree())
    assert [set(C) for C in good_D] == [set(C) for C in bad_D]
    assert binary_rank([set(C) for C in good_D]) == t
    H1_edges = set(word_edges(H1))
    for C in F:
        F_edges = set(word_edges(C))
        mixing = sum(sum(v in e for e in F_edges & H1_edges) == 1 for v in C)
        assert mixing >= 2 and mixing % 2 == 0
    for C in F:
        S = set(C)
        assert bad.subgraph(S).number_of_edges() == 9
        assert sum(1 for u, v in bad.edges() if (u in S) != (v in S)) == 2
    return good, good_D, (H1, H2), bad, bad_D


def sharp_frustration():
    # Four cyclic links, two privately subdivided branches per link.
    a, b = [4 + i for i in range(4)], [8 + i for i in range(4)]
    C0 = tuple(v for i in range(4) for v in (i, a[i]))
    C1 = tuple(v for i in range(4) for v in (i, b[i]))
    C2 = (a[0], b[2], 12)
    D = [C0, C1, C2]
    G = partition_graph(D)
    opt, nc = exact_optimum(G)
    assert len(opt) == 3
    tight_cactus = 0
    for j in range(4):
        connectors = [j, b[2], a[0]]
        mu, values = frustration(D, connectors)
        assert mu == 1 and all(v[0] == 0 for v in values)
        for B, v, words, out, eta in values:
            assert 3 <= 2 + B + v - eta
            if v == mu:
                assert eta == 0
                tight_cactus += 1
    return {"n": len(G), "m": G.number_of_edges(), "all_simple_cycles": nc,
            "optimum": len(opt), "ring_choices": 4, "frustration": 1,
            "tight_assignments_have_cactus_macrographs": tight_cactus}


def sharp_branching():
    connectors = [1, 2, 3]
    D = [(0, 4 + 2 * i, connectors[i - 1], connectors[i], 5 + 2 * i)
         for i in range(3)]
    G = partition_graph(D)
    assert G.degree(0) == 6
    mu, values = frustration(D, connectors)
    assert mu == 0 and all(v[0] == 1 for v in values)
    opt, nc = exact_optimum(G)
    assert len(opt) == 3
    return {"n": len(G), "m": G.number_of_edges(), "all_simple_cycles": nc,
            "optimum": 3, "branching": 1, "frustration": 0}


def two_port_barrier(k):
    # T_k from ResearchInterfaces, independently regenerated here.
    r = k + 1
    A = [r + 2 * i for i in range(r)]
    B = [r + 2 * i + 1 for i in range(r)]
    C0 = tuple(v for i in range(r) for v in (i, A[i]))
    C1 = tuple(v for i in range(r) for v in (i, B[i]))
    G = partition_graph([C0, C1])
    # For r=2 the cycle-word construction still gives four distinct paths.
    assert nx.is_biconnected(G)
    optimum, _ = exact_optimum(G)
    forced, nc = exact_optimum(G, forced_pair=(A[0], B[0]))
    assert len(optimum) == 2 and len(forced) == k + 1
    assert [C for C in all_cycles(G) if A[0] in C and B[0] in C] == [
        C for C in all_cycles(G) if set(C) == {0, 1, A[0], B[0]}]
    return {"k": k, "n": len(G), "unconstrained": 2,
            "with_two_ports_on_one_cycle": len(forced), "all_simple_cycles": nc}


def common_pole_packet_tests():
    tests = []
    for k in (1, 2, 5, 20):
        root = [(0, 2 + 2 * i, 1, 3 + 2 * i) for i in range(k)]
        fresh = 2 + 2 * k
        leaves = [(v,) + tuple(range(fresh + 4 * v, fresh + 4 * v + 4))
                  for v in (0, 1)]
        packets = [root] + [[C] for C in leaves]
        D = root + leaves
        G = partition_graph(D)
        root_graph = partition_graph(root)
        root_cycles = list(all_cycles(root_graph))
        assert len(root_cycles) == k * (2 * k - 1)
        assert all(len(C) == 4 for C in root_cycles)
        assert all(len(set(C) & set(T)) == 2 for C, T in combinations(root, 2))
        supports = [set().union(*(set(C) for C in P)) for P in packets]
        for i, (P, S) in enumerate(zip(packets, supports)):
            boundary = S & set().union(*(T for j, T in enumerate(supports) if j != i))
            assert all(any({u, v} <= set(C) for C in P)
                       for u, v in combinations(boundary, 2))
            assert 2 * len(P) <= len(S) - 1
        B = incidence_graph(supports, G)
        assert nx.is_forest(B)
        assert sum(len(S) - 1 for S in supports) == len(G) - 1
        lower = 0
        for E in nx.biconnected_component_edges(G):
            H = nx.Graph()
            H.add_edges_from(E)
            lower += max(d for _, d in H.degree()) // 2
        assert lower == len(D) == k + 2
        assert 2 * len(D) <= len(G) - 1
        if k <= 2:
            opt, _ = exact_optimum(G)
            assert len(opt) == len(D)
        tests.append({"k": k, "n": len(G), "optimum": len(D),
                      "canonical_overlap_chromatic": k,
                      "coarser_packet_overlap_chromatic": 1})
    return tests


def check_ring_packets():
    tests = 0
    for s in (3, 4, 7, 12):
        for size in (3, 5, 9):
            connectors = list(range(s))
            fresh = s
            packets = []
            for i in range(s):
                S = [connectors[i - 1], connectors[i]] + list(range(fresh, fresh + size - 2))
                fresh += size - 2
                packets.append(walecki(S))
            D = [C for P in packets for C in P]
            G = partition_graph(D)
            selected = [P[0] for P in packets]
            mu, values = frustration(selected, connectors)
            assert mu == 0 and all(B == 0 and v == 0 for B, v, *_ in values)
            out = values[0][3] + [C for P in packets for C in P[1:]]
            partition_graph(out, target=G.edges())
            assert len(out) == len(D) - s + 2
            tests += 1
    return tests


def main():
    here = Path(__file__).resolve().parent
    spec = here / "Spec.lean"
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_SHA256
    protected = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                 for p in here.iterdir() if p.is_file() and not p.name.startswith("ResearchIncidence")}
    rng = random.Random(20260829)
    report = {}

    atlas, indep = 0, 0
    for G in nx.graph_atlas_g():
        if not all(d % 2 == 0 for _, d in G.degree()):
            continue
        D, _ = exact_optimum(G)
        indep += packet_check(G, D)
        atlas += 1
    report["all_even_atlas_graphs_through_order_7"] = atlas
    report["independent_packet_families_in_exact_optima"] = indep

    random_rings, assignments, balancing = 0, 0, 0
    for _ in range(100):
        s = rng.randrange(3, 8)
        entries = []
        for _ in range(rng.randrange(0, 2 * s + 1)):
            size = rng.randrange(2, min(s, 4) + 1)
            I = rng.sample(range(s), size)
            signs = [rng.randrange(2) for _ in I]
            entries.append((I, signs))
        chords = []
        for i in range(s):
            possible = [j for j in range(s) if j not in ((i - 1) % s, i)]
            if possible and rng.random() < 0.25:
                chords.append((i, rng.choice(possible), rng.randrange(2)))
        D, x = make_ring(s, entries, rng, chords)
        mu, values = frustration(D, x)
        A, inc, B, constraints = ring_data(D, x)
        expected = sum((Fraction(1, 2 ** (len(L) - 1)) for _, L in constraints), Fraction())
        assert Fraction(sum(v[1] for v in values), len(values)) == expected
        assert mu <= expected
        assert all(v[0] == B for v in values)
        random_rings += 1
        assignments += len(values)
        balancing += weighted_balancing_check(D, x, rng)
    # More balanced signed forests: positive instances of the extension.
    for s in range(3, 9):
        for _ in range(5):
            entries = [([i, rng.randrange(i)], [rng.randrange(2), rng.randrange(2)])
                       for i in range(1, s)]
            D, x = make_ring(s, entries, rng)
            assert weighted_balancing_check(D, x, rng)
            balancing += 1
    report["arbitrary_ring_tests"] = random_rings
    report["all_binary_assignments_checked"] = assignments
    report["exact_rational_balanced_component_tests"] = balancing
    report["sharp_frustrated_optimum"] = sharp_frustration()
    report["sharp_branching_optimum"] = sharp_branching()
    report["homogeneous_packet_rings_recombined"] = check_ring_packets()
    report["nonhomogeneous_common_pole_packets"] = common_pole_packet_tests()
    report["two_port_minimum_preservation_barrier"] = [two_port_barrier(k) for k in range(2, 7)]

    hierarchy = []
    for h in range(1, 6):
        G, D, packets = laminar_partition(h)
        n = len(G)
        W = walecki(list(range(n)))
        assert len(W) == (n - 1) // 2
        sets = [set(C) for C in D]
        for S, T in combinations(sets, 2):
            assert not (S & T) or S <= T or T <= S
            assert len(S & T) != 1
        assert binary_rank(sets) == n // 3
        leaves = [set(range(i, i + 3)) for i in range(0, n, 3)]
        for S in sets:
            assert all(not (S & L) or L <= S for L in leaves)
        for S, depth, P in packets:
            H = partition_graph(P)
            # Every packet is itself certified optimal by its regular degree.
            assert len(P) == max(d for _, d in H.degree()) // 2
            assert len(S) == 3 ** (h - depth)
        incidence_beta = G.number_of_edges() - n - len(D) + 1
        squares = None
        if h <= 3:
            squares = four_cycle_span_dimension(D)
            assert squares == incidence_beta
        ring_tests = laminar_ring_checks(packets)
        hierarchy.append({"h": h, "n": n, "old_q": len(D),
                          "global_optimum": len(W), "incidence_rank": n // 3,
                          "distinct_support_packets": len(packets),
                          "proper_overlap_chromatic_and_fractional_chromatic": h,
                          "incidence_nullity": incidence_beta,
                          "square_span_dimension_checked": squares,
                          "laminar_ring_certificate_barrier_tests": ring_tests})
    report["laminar_complete_graph_hierarchy"] = hierarchy

    pairs = []
    for t in (2, 3, 4, 8, 20, 50):
        good, D, H, bad, D_bad = same_incidence_pair(t)
        if t == 2:
            opt, nc = exact_optimum(bad)
            assert len(opt) == t + 1
        pairs.append({"t": t, "n": len(good), "old_q": len(D),
                      "good_optimum": 2, "bad_optimum": t + 1,
                      "common_incidence_rank": t})
    report["identical_incidence_different_optima"] = pairs

    for name, digest in protected.items():
        assert hashlib.sha256((here / name).read_bytes()).hexdigest() == digest
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_SHA256
    report["protected_files_unchanged_during_checker"] = len(protected)
    report["spec_sha256"] = SPEC_SHA256
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
