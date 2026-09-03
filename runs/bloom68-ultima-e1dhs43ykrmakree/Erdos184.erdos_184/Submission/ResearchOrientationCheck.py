#!/usr/bin/env python3
"""Reproducible finite checks for ResearchOrientation.md; does not edit Spec.lean.

Python 3 + networkx only.  All mathematical claims have proofs in the note;
these checks are supplementary and use exact integer/rational arithmetic.
"""
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, product
from pathlib import Path
import json
import random

import networkx as nx

SPEC_SHA256 = "429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde"
RNG = random.Random(1842026)


def ue(u, v):
    assert u != v
    return frozenset((u, v))


def arcs(C):
    C = tuple(C)
    return list(zip(C, C[1:] + C[:1]))


def edges(C):
    return {ue(u, v) for u, v in arcs(C)}


def support(T):
    return {ue(u, v) for u, v in T}


def balance(T):
    b = Counter()
    for u, v in T:
        b[u] += 1
        b[v] -= 1
    return all(x == 0 for x in b.values())


def assert_orientation(E, T):
    assert len(T) == len(E) and support(T) == E


def assert_partition(E, D, T=None):
    count = Counter()
    for C in D:
        assert len(C) >= 3 and len(C) == len(set(C))
        count.update(ue(u, v) for u, v in arcs(C))
        if T is not None:
            assert set(arcs(C)) <= T
    assert count == Counter({e: 1 for e in E})


def euler_orientation(G):
    assert all(d % 2 == 0 for _, d in G.degree())
    T = set()
    for vs in nx.connected_components(G):
        H = G.subgraph(vs).copy()
        if H.number_of_edges():
            T.update(nx.eulerian_circuit(H, source=min(vs)))
    assert_orientation({ue(u, v) for u, v in G.edges()}, T)
    assert balance(T)
    return T


def directed_partition(T):
    assert balance(T)
    DG = nx.DiGraph()
    DG.add_edges_from(sorted(T))
    D = []
    for vs in nx.weakly_connected_components(DG):
        H = DG.subgraph(vs).copy()
        source = min(vs)
        stack, pos = [source], {source: 0}
        for u, v in nx.eulerian_circuit(H, source=source):
            assert stack[-1] == u
            if v in pos:
                j = pos[v]
                D.append(tuple(stack[j:]))
                for w in stack[j + 1:]:
                    del pos[w]
                stack = stack[:j + 1]
            else:
                pos[v] = len(stack)
                stack.append(v)
        assert stack == [source]
    assert_partition(support(T), D, T)
    return D


def flip_from_representatives(D, F):
    """F is already an Eulerian orientation, at most one edge per old cycle."""
    assert balance(F)
    E = set().union(*(edges(C) for C in D)) if D else set()
    assert_partition(E, D)
    assert support(F) <= E
    T0, used = set(), set()
    F_by_edge = {ue(u, v): (u, v) for u, v in F}
    for i, C in enumerate(D):
        marked = [F_by_edge[e] for e in edges(C) if e in F_by_edge]
        assert len(marked) <= 1
        if marked:
            u, v = marked[0]
            used.add(i)
            old = C if (v, u) in arcs(C) else tuple(reversed(C))
        else:
            old = C
        T0.update(arcs(old))
    assert_orientation(E, T0)
    assert balance(T0)
    T = T0 - {(v, u) for u, v in F}
    T.update(F)
    assert_orientation(E, T)
    assert balance(T)
    T_by_edge = {ue(u, v): (u, v) for u, v in T}
    for i, C in enumerate(D):
        fwd = len(set(arcs(C)) & T)
        if i in used:
            assert fwd in {1, len(C) - 1}
            H = nx.DiGraph([T_by_edge[e] for e in edges(C)])
            assert nx.is_directed_acyclic_graph(H)
        else:
            assert fwd in {0, len(C)}
    P = T - F
    # This includes the untouched old cycles, which are separately balanced.
    assert balance(P)
    return T, T0, used


def greedy_representatives(n, D):
    remaining = set(range(len(D)))
    F, Q = set(), []
    while remaining:
        H = nx.Graph()
        H.add_nodes_from(range(n))
        for i in sorted(remaining):
            u, v = RNG.choice(arcs(D[i]))
            H.add_edge(u, v, color=i)
        found = nx.cycle_basis(H)
        if not found:
            assert len(remaining) <= max(0, n - 1)
            break
        C = max(found, key=len)
        colors = {H[u][v]["color"] for u, v in arcs(C)}
        assert len(colors) == len(C)
        assert colors <= remaining
        remaining -= colors
        F.update(arcs(C))
        Q.append(tuple(C))
    assert_partition(support(F), Q, F)
    T, _, used = flip_from_representatives(D, F)
    assert used == set(range(len(D))) - remaining
    return T, F, Q, remaining


def maximal_triangle_representatives(n, D):
    """Use incidence cycles, so the unused incidence graph really is a forest."""
    assert all(len(C) == 3 for C in D)
    remaining = set(range(len(D)))
    F, Q = set(), []
    while True:
        B = nx.Graph()
        B.add_nodes_from((0, v) for v in range(n))
        B.add_nodes_from((1, i) for i in remaining)
        B.add_edges_from(((0, v), (1, i)) for i in remaining for v in D[i])
        cs = nx.cycle_basis(B)
        if not cs:
            assert 2 * len(remaining) == n - nx.number_connected_components(B)
            break
        W = cs[0]
        start = next(i for i, z in enumerate(W) if z[0] == 0)
        W = W[start:] + W[:start]
        C = tuple(z[1] for z in W[::2])
        colors = {z[1] for z in W[1::2]}
        assert len(C) >= 3 and len(colors) == len(C)
        for j, (u, v) in enumerate(arcs(C)):
            assert {u, v} <= set(D[W[2*j + 1][1]])
        F.update(arcs(C))
        Q.append(C)
        remaining -= colors
    T, _, used = flip_from_representatives(D, F)
    assert len(remaining) <= max(0, (n - 1) // 2) if D else not remaining
    assert used == set(range(len(D))) - remaining
    return T, F, Q, remaining


def phased_cycles(layers):
    """Optimal factorization of a complete cyclic even-layer blow-up."""
    assert len(layers) >= 4 and len(layers) % 2 == 0
    assert len(set(z for L in layers for z in L)) == sum(map(len, layers))
    assert len({len(L) for L in layers[::2]}) == 1
    assert len({len(L) for L in layers[1::2]}) == 1
    T = set().union(*(set(product(layers[j], layers[(j+1) % len(layers)]))
                      for j in range(len(layers))))
    if len(layers[0]) > len(layers[1]):
        layers = layers[1:] + layers[:1]
    b, a, h = len(layers[0]), len(layers[1]), len(layers)//2
    assert 1 <= b <= a
    D = [tuple(z for j in range(b) for k in range(h)
               for z in (layers[2*k][j], layers[2*k+1][(i+j) % a]))
         for i in range(a)]
    assert balance(T)
    assert_partition(support(T), D, T)
    assert len(D) == a and all(len(C) == 2*h*b for C in D)
    return T, D


def phase_packet(a, b, h=2, offset=0):
    layers, start = [], offset
    for _ in range(h):
        layers.append(list(range(start, start+b)))
        start += b
        layers.append(list(range(start, start+a)))
        start += a
    return phased_cycles(layers)


def global_family(a, r):
    """G_{a,r}; its dense specialization a=2r is K_{2r,2r,2r}."""
    assert 1 <= 2*r <= a
    X = list(range(a))
    Y = list(range(a, 2*a))
    A = list(range(2*a, 2*a+r))
    B = list(range(2*a+r, 2*a+2*r))
    D0, D1, Q = [], [], []
    for j in range(r):
        for i in range(a):
            D0.extend([(X[i], A[j], Y[(i+2*j) % a]),
                       (Y[(i+2*j+1) % a], B[j], X[i])])
            D1.extend([(X[i], Y[(i+2*j) % a], B[j]),
                       (Y[(i+2*j+1) % a], X[i], A[j])])
        Q.append(tuple(z for t in range(a)
                       for z in (X[(-t) % a], Y[(-t+2*j) % a])))
    F = set().union(*(set(arcs(C)) for C in Q))
    P = (set(product(X, A)) | set(product(A, Y)) |
         set(product(Y, B)) | set(product(B, X)))
    T = F | P
    E = support(T)
    assert len(E) == 6*a*r and len(D0) == 2*a*r
    assert balance(F) and balance(P) and balance(T)
    assert_partition(E, D0)
    assert_partition(E, D1, T)
    assert_partition(support(F), Q, F)
    assert not {frozenset(C) for C in D0} & {frozenset(C) for C in D1}
    Tcheck, T0, used = flip_from_representatives(D0, F)
    assert Tcheck == T and len(used) == len(D0)
    reverseF = {(v, u) for u, v in F}
    Tback, _, used1 = flip_from_representatives(D1, reverseF)
    assert Tback == T0 and len(used1) == len(D1)
    # D0 is cyclic in T0, although its tuples above specify the two forward paths.
    assert all(len(set(arcs(C)) & T0) in {0, 3} for C in D0)
    Dlocal = [tuple((X[i], A[j], Y[i], B[j]))
              for j in range(r) for i in range(a)]
    assert_partition(E, Q + Dlocal, T)
    Dglobal = [tuple(z for j in range(r)
                     for z in (A[j], Y[(i+j) % a], B[j], X[(i+j) % a]))
               for i in range(a)]
    assert_partition(E, Q + Dglobal, T)
    assert len(Q + Dlocal) == r + a*r
    assert len(Q + Dglobal) == a + r == len(X + Y + A + B) // 2
    G = nx.Graph()
    G.add_edges_from(tuple(e) for e in E)
    assert all(G.degree(v) == 4*r for v in X + Y)
    assert all(G.degree(v) == 2*a for v in A + B)
    weights = [sum((Fraction(1, G.degree(v)) for v in C), Fraction())
               for C in Q + Dglobal]
    assert set(weights) <= {Fraction(a, 2*r), Fraction(1, 2) + Fraction(r, a)}
    assert min(weights) >= Fraction(1, 2)
    assert sum(weights) == Fraction(len(G), 2)
    rhoF = sum((Fraction(sum(v in e for e in support(F)), G.degree(v))
                for v in G), Fraction())
    rhoP = sum((Fraction(sum(v in e for e in support(P)), G.degree(v))
                for v in G), Fraction())
    assert rhoF == a and rhoP == a + 2*r
    optimal_hamiltonian_cycles = None
    if a == 2*r:
        assert set(weights) == {Fraction(1)}
        assert all(G.has_edge(u, v) == ((u // (2*r)) != (v // (2*r)))
                   for u, v in combinations(range(6*r), 2))
        if r <= 3:
            assert nx.node_connectivity(G) == 4*r
        if r >= 2:
            Fpartial = set().union(*(set(arcs(C)) for C in Q[:-1]))
            Tpartial, _, usedpartial = flip_from_representatives(D0, Fpartial)
            split = 2*a*(r-1)
            Dpartial = D1[:split] + D0[split:]
            assert_partition(E, Dpartial, Tpartial)
            Treturn, _, _ = flip_from_representatives(Dpartial, {(v, u) for u, v in Fpartial})
            assert Treturn == T0
            assert len(D0) - len(usedpartial) == 4*r <= 6*r-1
        X0, X1, Y0, Y1 = X[::2], X[1::2], Y[::2], Y[1::2]
        T1, H1 = phased_cycles([X0, A, Y0, X1, Y1, B])
        T2, H2 = phased_cycles([X0, Y0, B, X1, A, Y1])
        assert not T1 & T2 and T1 | T2 == T
        assert_partition(E, H1 + H2, T)
        assert len(H1 + H2) == 2*r == max(dict(G.degree()).values()) // 2
        assert all(len(C) == 6*r for C in H1 + H2)
        assert all(sum((Fraction(1, G.degree(v)) for v in C), Fraction()) == Fraction(3, 2)
                   for C in H1 + H2)
        optimal_hamiltonian_cycles = 2*r
    # Every batch of b original rainbow expansions is D(a,b), forcing >=a cycles.
    for b in sorted({1, r, max(1, r//2)}):
        PB = (set(product(X, A[:b])) | set(product(A[:b], Y)) |
              set(product(Y, B[:b])) | set(product(B[:b], X)))
        DB = [tuple(z for j in range(b)
                    for z in (A[j], Y[(i+j) % a], B[j], X[(i+j) % a]))
              for i in range(a)]
        assert_partition(support(PB), DB, PB)
        assert len(PB) == 4*a*b and len(DB) == a
    return dict(a=a, r=r, n=2*a+2*r, edges=len(E), old_triangles=len(D0),
                rainbow_cycles=r, independent_lift_cycles=r+a*r,
                globally_coupled_cycles=a+r, minimum_weight=str(min(weights)),
                optimal_hamiltonian_cycles=optimal_hamiltonian_cycles)


def inverse_triangle_flip(D, T):
    """Every balanced orientation of a triangle partition has the shortcut form."""
    E = set().union(*(edges(C) for C in D)) if D else set()
    assert_orientation(E, T)
    assert balance(T)
    F, cyclic, ordered = set(), 0, []
    T_by_edge = {ue(u, v): (u, v) for u, v in T}
    for C in D:
        CE = {T_by_edge[e] for e in edges(C)}
        out = {v: sum(u == v for u, w in CE) for v in C}
        if set(out.values()) == {1}:
            cyclic += 1
            ordered.append(C if set(arcs(C)) <= T else tuple(reversed(C)))
        else:
            ordered.append(C)
            source = next(v for v in C if out[v] == 2)
            sink = next(v for v in C if out[v] == 0)
            assert (source, sink) in T
            F.add((source, sink))
    assert balance(F)
    recovered, _, used = flip_from_representatives(ordered, F)
    assert recovered == T
    assert len(F) + cyclic == len(D)
    directed_partition(F)
    return len(F), cyclic


def proper_complete_edge_color(n, u, v):
    if n % 2:
        return ((u + v) * ((n+1)//2)) % n
    infinity = n-1
    if u == infinity:
        return v
    if v == infinity:
        return u
    modulus = n-1
    return ((u + v) * ((modulus+1)//2)) % modulus


def universal_embedding(n, D):
    assert balance(D)
    old, T, incident_colors = [], set(), {v: set() for v in range(n)}
    for u, v in sorted(D):
        color = proper_complete_edge_color(n, u, v)
        assert color not in incident_colors[u] and color not in incident_colors[v]
        incident_colors[u].add(color)
        incident_colors[v].add(color)
        z = n + color
        old.append((u, z, v))
        T.update([(u, v), (u, z), (z, v)])
    E = support(T)
    assert len(E) == 3 * len(D)
    assert max((v for e in E for v in e), default=-1) < 2*n
    assert balance(T)
    assert_partition(E, old)
    Tcheck, _, used = flip_from_representatives(old, D)
    assert Tcheck == T and len(used) == len(old)
    assert {(u, v) for u, v in T if u < n and v < n} == D
    T_by_edge = {ue(u, v): (u, v) for u, v in T}
    assert all(nx.is_directed_acyclic_graph(nx.DiGraph(
        [T_by_edge[e] for e in edges(C)])) for C in old)
    return len(E)


def regular_tournaments(n):
    def rec(v, need, T):
        if v == n:
            if not any(need):
                yield T
            return
        rest = list(range(v+1, n))
        if not 0 <= need[v] <= len(rest):
            return
        for out in combinations(rest, need[v]):
            S, req, new = set(out), need.copy(), set()
            req[v] = 0
            for u in rest:
                if u in S:
                    new.add((v, u))
                else:
                    req[u] -= 1
                    new.add((u, v))
            if all(0 <= req[u] < len(rest) for u in rest):
                yield from rec(v+1, req, T | new)
    yield from rec(0, [n//2] * n, set())


def tournament_checks():
    results = []
    for n in [3, 5, 7]:
        counts, packing_sizes = 0, []
        for T in regular_tournaments(n):
            tri, vertex_counts = [], Counter()
            for vs in combinations(range(n), 3):
                CE = {(u, v) for u in vs for v in vs if (u, v) in T}
                if all(sum(u == w for u, v in CE) == 1 for w in vs):
                    tri.append(CE)
                    vertex_counts.update(vs)
            assert len(tri) * 24 == n * (n*n-1)
            assert all(vertex_counts[v] * 8 == n*n-1 for v in range(n))
            used, packing = set(), []
            for C in tri:
                if not C & used:
                    used |= C
                    packing.append(C)
            assert 36 * len(packing) >= n*(n+1)
            assert balance(T - used)
            assert all(C & used for C in tri)
            directed_partition(T - used)
            packing_sizes.append(len(packing))
            counts += 1
        assert counts == {3: 2, 5: 24, 7: 2640}[n]
        results.append(dict(n=n, orientations=counts,
                            min_greedy_triangles=min(packing_sizes),
                            max_greedy_triangles=max(packing_sizes)))
    # Sharp feedback-arc lower bound, attained by the cyclic tournament.
    for n in range(3, 52, 2):
        s = n//2
        T = {(u, (u+d) % n) for u in range(n) for d in range(1, s+1)}
        backward = {(u, v) for u, v in T if u > v}
        assert balance(T) and len(backward) == s*(s+1)//2
        assert nx.is_directed_acyclic_graph(nx.DiGraph(T - backward))
    return results


def orientation_extension_checks():
    count, feasible = 0, 0
    for n in [3, 5]:
        E = [ue(u, v) for u, v in combinations(range(n), 2)]
        for _ in range(160):
            H, R = set(), []
            for e in E:
                u, v = sorted(e)
                typ = RNG.randrange(3)
                if typ == 0:
                    R.append((u, v))
                else:
                    H.add((u, v) if typ == 1 else (v, u))
            b = Counter()
            for u, v in H:
                b[u] += 1
                b[v] -= 1
            cuts_ok = True
            for mask in range(1 << n):
                S = {v for v in range(n) if mask >> v & 1}
                cut = sum((u in S) != (v in S) for u, v in R)
                if abs(sum(b[v] for v in S)) > cut:
                    cuts_ok = False
                    break
            completion = False
            for bits in product([0, 1], repeat=len(R)):
                T = H | {(v, u) if z else (u, v) for z, (u, v) in zip(bits, R)}
                if balance(T):
                    completion = True
                    break
            assert cuts_ok == completion
            count += 1
            feasible += completion
    return dict(cases=count, feasible=feasible)


def main():
    spec = Path(__file__).with_name("Spec.lean")
    assert sha256(spec.read_bytes()).hexdigest() == SPEC_SHA256
    atlas, generic, triangle, embeddings, inverse = 0, 0, 0, 0, 0
    for G in nx.graph_atlas_g():
        if not len(G) or any(d % 2 for _, d in G.degree()):
            continue
        T = euler_orientation(G)
        D = directed_partition(T)
        greedy_representatives(len(G), D)
        atlas += 1
    for n in [6, 9, 12, 20, 31, 48]:
        for _ in range(8):
            G = nx.Graph()
            G.add_nodes_from(range(n))
            D = []
            for attempt in range(20*n*n):
                C = tuple(RNG.sample(range(n), RNG.randint(3, min(7, n))))
                if not any(G.has_edge(u, v) for u, v in arcs(C)):
                    D.append(C)
                    G.add_edges_from(arcs(C))
            T, F, Q, remaining = greedy_representatives(n, D)
            # Reorienting F by another Euler tour also preserves the flip conclusion.
            FG = nx.Graph()
            FG.add_nodes_from(range(n))
            FG.add_edges_from(tuple(e) for e in support(F))
            flip_from_representatives(D, euler_orientation(FG))
            directed_partition(T)
            universal_embedding(n, euler_orientation(G))
            generic += 1
            embeddings += 1
    for n in [7, 12, 21, 32]:
        for _ in range(6):
            G = nx.Graph()
            G.add_nodes_from(range(n))
            D = []
            candidates = list(combinations(range(n), 3))
            RNG.shuffle(candidates)
            for C in candidates:
                if not any(G.has_edge(u, v) for u, v in arcs(C)):
                    D.append(C)
                    G.add_edges_from(arcs(C))
            maximal_triangle_representatives(n, D)
            inverse_triangle_flip(D, euler_orientation(G))
            triangle += 1
            inverse += 1
    phase = 0
    for a in range(1, 17):
        for b in range(1, 17):
            phase_packet(a, b)
            phase += 1
    for h in [3, 4, 6]:
        for a in range(1, 7):
            for b in range(1, 7):
                phase_packet(a, b, h)
                phase += 1
    family = []
    pairs = {(2*r, r) for r in list(range(1, 13)) + [16, 24, 32]}
    pairs |= {(a, r) for r in [1, 2, 3, 5, 8] for a in [2*r+1, 3*r, 5*r+2]}
    for a, r in sorted(pairs):
        family.append(global_family(a, r))
    results = dict(
        atlas_even_graphs=atlas, generic_random_graphs=generic,
        maximal_triangle_selection_cases=triangle,
        inverse_triangle_flip_cases=inverse, linear_vertex_embeddings=embeddings,
        phase_packets=phase, global_family=family,
        regular_tournaments=tournament_checks(),
        orientation_extensions=orientation_extension_checks(),
        specification_sha256=SPEC_SHA256,
    )
    assert sha256(spec.read_bytes()).hexdigest() == SPEC_SHA256
    print(json.dumps(results, indent=2))
    print("All ResearchOrientation checks passed; Spec.lean unchanged.")


if __name__ == "__main__":
    main()
