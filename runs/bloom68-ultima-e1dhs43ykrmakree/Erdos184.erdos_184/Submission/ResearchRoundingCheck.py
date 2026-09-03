#!/usr/bin/env python3
"""Targeted checks for ResearchRounding.md.  Never edits Spec.lean.

Python 3, networkx, numpy, scipy.  Numerical solvers propose witnesses;
all retained primal/dual witnesses are rechecked with exact Fractions.
The general assertions, especially the Petersen-ring lower bound and the
series-parallel theorem, have separate proofs in the Markdown document.
"""
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, count, product
from math import factorial
from pathlib import Path
import json
import random

import networkx as nx
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, linprog, milp
from scipy.sparse import csc_matrix

SPEC_SHA256 = "429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde"
RNG = random.Random(184)


def edge(u, v):
    assert u != v
    return tuple(sorted((u, v)))


def cycle_edges(C):
    C = tuple(C)
    assert len(C) >= 3 and len(C) == len(set(C))
    return frozenset(edge(u, v) for u, v in zip(C, C[1:] + C[:1]))


def path_edges(P):
    assert len(P) == len(set(P))
    return frozenset(edge(u, v) for u, v in zip(P, P[1:]))


def graph_edges(G):
    return frozenset(edge(u, v) for u, v in G.edges())


def assert_partition(G, D, paths=(), terminals=None):
    used = Counter(e for C in D for e in cycle_edges(C))
    for P in paths:
        if terminals is not None:
            assert (P[0], P[-1]) == terminals
        used.update(path_edges(P))
    assert used == Counter({e: 1 for e in graph_edges(G)})


def all_cycles(G, hamilton_only=False):
    """Exactly once per undirected simple cycle; integer-labelled graphs."""
    for s in sorted(G):
        if hamilton_only and s != min(G):
            break

        def dfs(P, used):
            for v in sorted(G[P[-1]]):
                if v == s:
                    if (len(P) >= 3 and P[1] < P[-1]
                            and (not hamilton_only or len(P) == len(G))):
                        yield tuple(P)
                elif v > s and v not in used:
                    yield from dfs(P + [v], used | {v})

        yield from dfs([s], {s})


def assert_dual(G, cycles, y, value=None):
    assert set(y) == set(graph_edges(G))
    assert all(sum((y[e] for e in cycle_edges(C)), F()) <= 1 for C in cycles)
    if value is not None:
        assert sum(y.values(), F()) == value


def incidence(G, cycles):
    es = sorted(graph_edges(G))
    ix = {e: i for i, e in enumerate(es)}
    rows, cols = [], []
    for j, C in enumerate(cycles):
        for e in cycle_edges(C):
            rows.append(ix[e])
            cols.append(j)
    A = csc_matrix((np.ones(len(rows)), (rows, cols)),
                   shape=(len(es), len(cycles)))
    return A, es


def walecki(r):
    D = []
    for i in range(r):
        C = [2*r, i]
        for j in range(1, r):
            C.extend(((i-j) % (2*r), (i+j) % (2*r)))
        C.append((i-r) % (2*r))
        D.append(tuple(C))
    assert_partition(nx.complete_graph(2*r+1), D)
    return D


# ---------- Exact series-parallel path/cycle dynamic program ----------

@dataclass
class Network:
    kind: str
    s: int
    t: int
    G: object
    left: object = None
    right: object = None
    capacity: int = 1
    low: int = 1
    parity: int = 1
    index: int = -1


def expression_parity(e):
    if e == "E":
        return 1
    a, b = expression_parity(e[1]), expression_parity(e[2])
    if e[0] == "S":
        assert a == b, "The series junction must have even degree."
        return a
    return (a+b) % 2


def build_network(e, s=0, t=1, ids=None):
    """Subdivide every leaf edge once, so every tested graph is simple."""
    if ids is None:
        ids = count(2)
    if e == "E":
        w = next(ids)
        return Network("E", s, t, nx.Graph([(s, w), (w, t)]))
    if e[0] == "S":
        w = next(ids)
        a = build_network(e[1], s, w, ids)
        b = build_network(e[2], w, t, ids)
        assert a.parity == b.parity
        return Network("S", s, t, nx.compose(a.G, b.G), a, b,
                       min(a.capacity, b.capacity), max(a.low, b.low), a.parity)
    a = build_network(e[1], s, t, ids)
    b = build_network(e[2], s, t, ids)
    return Network("P", s, t, nx.compose(a.G, b.G), a, b,
                   a.capacity+b.capacity, 0, (a.parity+b.parity) % 2)


def sp_value(N, p):
    p = F(p)
    assert N.low <= p <= N.capacity
    if N.kind == "E":
        return F(0)
    if N.kind == "S":
        return sp_value(N.left, p) + sp_value(N.right, p)
    a = min(F(N.left.capacity), p+N.right.capacity)
    b = min(F(N.right.capacity), p+N.left.capacity)
    return sp_value(N.left, a) + sp_value(N.right, b) + (a+b-p)/2


def sp_partition(N, p):
    assert N.low <= p <= N.capacity and p % 2 == N.parity
    if N.kind == "E":
        return [tuple(nx.shortest_path(N.G, N.s, N.t))], []
    if N.kind == "S":
        P1, D1 = sp_partition(N.left, p)
        P2, D2 = sp_partition(N.right, p)
        return [a+b[1:] for a, b in zip(P1, P2)], D1+D2
    a = min(N.left.capacity, p+N.right.capacity)
    b = min(N.right.capacity, p+N.left.capacity)
    assert (a+b-p) % 2 == 0
    h = (a+b-p)//2
    P1, D1 = sp_partition(N.left, a)
    P2, D2 = sp_partition(N.right, b)
    D = D1+D2+[x+y[-2:0:-1] for x, y in zip(P1[:h], P2[:h])]
    return P1[h:]+P2[h:], D


def compact_sp_dual(N, p):
    """Solve the O(tree-size) path-bound dual, then verify it exactly."""
    nodes = []

    def visit(T):
        T.index = len(nodes)
        nodes.append(T)
        if T.kind != "E":
            visit(T.left)
            visit(T.right)

    visit(N)
    obj = np.array([-1.0 if T.kind == "E" else 0.0 for T in nodes])
    obj[0] += float(p)
    rows, rhs = [], []
    for T in nodes:
        if T.kind == "E":
            continue
        i, a, b = T.index, T.left.index, T.right.index
        if T.kind == "S":
            row = np.zeros(len(nodes))
            row[a] = row[b] = 1
            row[i] = -1
            rows.append(row)
            rhs.append(0)
        else:
            for v in (a, b):
                row = np.zeros(len(nodes))
                row[v], row[i] = 1, -1
                rows.append(row)
                rhs.append(0)
            row = np.zeros(len(nodes))
            row[a] = row[b] = 1
            rows.append(row)
            rhs.append(1)
    result = linprog(obj, A_ub=np.array(rows) if rows else None,
                     b_ub=np.array(rhs) if rhs else None,
                     bounds=(None, None), method="highs")
    assert result.success, result.message
    alpha = [F(float(v)).limit_denominator(100000) for v in result.x]
    for row, b in zip(rows, rhs):
        assert sum((int(t)*v for t, v in zip(row, alpha)), F()) <= b
    y = {}
    for T in nodes:
        if T.kind == "E":
            for e in graph_edges(T.G):
                assert e not in y
                y[e] = alpha[T.index]/2
    assert sum(y.values(), F()) - F(p)*alpha[0] == sp_value(N, p)
    return y, alpha[0]


def check_sp():
    integral_states = fractional_states = eulerian_networks = 0
    for _ in range(200):
        pieces = ["E"] * RNG.randint(2, 8)
        while len(pieces) > 1:
            a = pieces.pop(RNG.randrange(len(pieces)))
            b = pieces.pop(RNG.randrange(len(pieces)))
            same = expression_parity(a) == expression_parity(b)
            kind = "S" if same and RNG.randrange(2) else "P"
            pieces.append((kind, a, b))
        N = build_network(pieces[0])
        assert all(d % 2 == 0 for v, d in N.G.degree() if v not in (0, 1))
        assert N.capacity % 2 == N.parity
        if N.parity == 0:
            eulerian_networks += 1
            assert N.low == 0
        cycles = list(all_cycles(N.G))
        paths = list(nx.all_simple_paths(N.G, 0, 1))
        for p in range(N.low, N.capacity+1):
            if p % 2 != N.parity:
                continue
            P, D = sp_partition(N, p)
            assert len(P) == p and len(D) == sp_value(N, p)
            assert_partition(N.G, D, P, (0, 1))
            y, a = compact_sp_dual(N, p)
            assert_dual(N.G, cycles, y)
            assert all(sum((y[e] for e in path_edges(Q)), F()) <= a for Q in paths)
            integral_states += 1
        for p in (F(N.low), F(N.low+N.capacity, 2), F(N.capacity)):
            y, a = compact_sp_dual(N, p)
            assert_dual(N.G, cycles, y)
            assert all(sum((y[e] for e in path_edges(Q)), F()) <= a for Q in paths)
            fractional_states += 1
    return {"networks": 200, "Eulerian_networks": eulerian_networks,
            "integral_states": integral_states, "fractional_states": fractional_states}


# ---------- Theta chains: exact values and indispensable signed prices ----------

def theta_chain(k, a, b):
    assert k >= 1 and a >= 1 and b >= 1 and (a-b) % 2 == 0
    ids = count(k+1)
    mids = [[next(ids) for _ in range(a)] for _ in range(k)]
    ret = [None] if b == 1 else [next(ids) for _ in range(b)]
    G = nx.Graph()
    branches = []
    for i in range(k):
        row = []
        for j in range(a):
            P = (i, mids[i][j], i+1)
            G.add_edges_from(zip(P, P[1:]))
            row.append(P)
        branches.append(row)
    returns = []
    for w in ret:
        P = (0, k) if w is None else (0, w, k)
        G.add_edges_from(zip(P, P[1:]))
        returns.append(P)

    def long_cycle(choices, j):
        P = [0]
        for i, z in enumerate(choices):
            P.extend((mids[i][z], i+1))
        return tuple(P) + returns[j][-2:0:-1]

    local = [(i, mids[i][j], i+1, mids[i][z])
             for i in range(k) for j, z in combinations(range(a), 2)]
    local_return = [returns[j] + returns[z][-2:0:-1]
                    for j, z in combinations(range(b), 2)]
    cycles = local + local_return + [long_cycle(z, j)
              for z in product(range(a), repeat=k) for j in range(b)]
    q = min(a, b)
    D = [long_cycle((j,)*k, j) for j in range(q)]
    for i in range(k):
        for j in range(q, a, 2):
            D.append((i, mids[i][j], i+1, mids[i][j+1]))
    for j in range(q, b, 2):
        D.append(returns[j] + returns[j+1][-2:0:-1])
    value = q + k*(a-q)//2 + (b-q)//2
    forward_price = F(1, 2) if a >= b else F(1, 2*k)
    return_price = 1-F(k, 2) if a >= b else F(1, 2)
    y = {}
    for row in branches:
        for P in row:
            for e in path_edges(P):
                y[e] = forward_price/2
    for P in returns:
        for e in path_edges(P):
            y[e] = return_price/(len(P)-1)
    assert len(D) == value
    assert_partition(G, D)
    assert_dual(G, cycles, y, value)
    assert all(d % 2 == 0 for _, d in G.degree())
    return G, cycles, D, y, branches, returns, long_cycle


def check_theta_chains():
    cases = 0
    for k in range(1, 6):
        for a, b in ((3, 1), (4, 2), (5, 1), (5, 3), (3, 5), (2, 4), (2, 2)):
            G, cycles, D, y, branches, returns, make_long = theta_chain(k, a, b)
            # Exact positive-support optimum used in the forced-sign proof.
            if a > b:
                fractional_load = Counter()
                fractional_cost = F()
                for i in range(k):
                    for j, z in combinations(range(a), 2):
                        C = (i, branches[i][j][1], i+1, branches[i][z][1])
                        x = F(a-b, a*(a-1))
                        fractional_cost += x
                        for e in cycle_edges(C):
                            fractional_load[e] += x
                for choices in product(range(a), repeat=k):
                    for j in range(b):
                        C = make_long(choices, j)
                        x = F(1, a**k)
                        fractional_cost += x
                        for e in cycle_edges(C):
                            fractional_load[e] += x
                assert fractional_load == Counter({e: F(1) for e in graph_edges(G)})
                assert fractional_cost == len(D)
            # Independently enumerate ALL simple cycles in the smaller cases.
            if k <= 3:
                assert {cycle_edges(C) for C in cycles} == {
                    cycle_edges(C) for C in all_cycles(G)}
            if (a, b) == (3, 1):
                odd = [make_long((j,)*k, 0) for j in range(3)]
                cover = Counter(e for C in odd for e in cycle_edges(C))
                assert all(v % 2 == 1 for v in cover.values())
                e0 = edge(0, k)
                assert cover[e0] == 3 and all(v == 1 for e, v in cover.items() if e != e0)
                assert y[e0] == 1-F(k, 2)
                uniform = {e: F(1, len(C)) for C in D for e in cycle_edges(C)}
                alternate = make_long((1,)*k, 0)
                assert sum(uniform[e] for e in cycle_edges(alternate)) == F(k, 2)+F(1, 2*k+1)
                if k >= 2:
                    nonneg = {e: F(1, 2*k) for row in branches for P in row for e in path_edges(P)}
                    nonneg[e0] = F(0)
                    assert_dual(G, cycles, nonneg, 3)
            if (a, b) == (4, 2):
                residual = returns[0] + returns[1][-2:0:-1]
                assert sum(y[e] for e in cycle_edges(residual)) == 2-k
                packing = [(i, branches[i][j][1], i+1, branches[i][j+1][1])
                           for i in range(k) for j in (0, 2)]
                assert len(packing) == 2*k
                assert_partition(G, packing+[residual])
                assert len(packing)-len(D) == k-2
            cases += 1
    return {"families": cases, "independently_enumerated_cases": 21}


# ---------- K5 basic point and local transition/blossom obstruction ----------

def check_k5():
    G = nx.complete_graph(5)
    support = [(0, 1, 2, 3, 4), (0, 1, 3, 4, 2), (0, 1, 4, 2, 3),
               (0, 2, 1, 4, 3), (0, 2, 3, 1, 4), (0, 3, 1, 2, 4)]
    A, es = incidence(G, support)
    B = A.toarray().astype(int)
    assert np.all(B.sum(axis=1) == 3)
    assert np.array_equal(B.T @ B, 3*np.eye(6, dtype=int)+2*np.ones((6, 6), dtype=int))
    assert all(len(cycle_edges(C) & cycle_edges(D)) == 2 for C, D in combinations(support, 2))
    assert_partition(G, walecki(2))
    assert_dual(G, list(all_cycles(G)), {e: F(1, 5) for e in es}, 2)
    # The series-parallel theorem also does not imply polytope integrality.
    H = nx.Graph((s, v) for s in (0, 1) for v in range(2, 8))
    half = [(0, a, 1, b) for triple in ((2, 3, 4), (5, 6, 7))
            for a, b in combinations(triple, 2)]
    A, _ = incidence(H, half)
    B = A.toarray().astype(int)
    assert np.all(B.sum(axis=1) == 2)
    block = 2*np.eye(3, dtype=int)+2*np.ones((3, 3), dtype=int)
    assert np.array_equal(B.T @ B, np.block([[block, np.zeros((3, 3), dtype=int)],
                                            [np.zeros((3, 3), dtype=int), block]]))
    assert_partition(H, [(0, 2, 1, 5), (0, 3, 1, 6), (0, 4, 1, 7)])
    assert_dual(H, list(all_cycles(H)),
                {e: F(1, 2) if 0 in e else F(0) for e in graph_edges(H)}, 3)
    return {"basic_variables": 6, "coefficient": "1/3", "rank": 6,
            "c_and_cf": 2, "SP_half_integral_basic_example_checked": True}


def check_transition_extension():
    sizes = []
    for N in (4, 6, 8):
        G = nx.complete_graph(N+1)
        if N == 4:
            M = {e: F(1, 3) for e in combinations(range(1, 5), 2)}
        else:
            M = {e: F(1, 2) for A in ((1, 2, 3), (4, 5, 6)) for e in combinations(A, 2)}
            if N == 8:
                M[(7, 8)] = F(1)
        assert all(sum(w for e, w in M.items() if v in e) == 1 for v in range(1, N+1))
        loads = Counter()
        transition = Counter()
        total = F()
        support_size = 0
        for C in all_cycles(G, hamilton_only=True):
            pair = edge(C[1], C[-1])
            x = M.get(pair, F()) / factorial(N-2)
            if not x:
                continue
            total += x
            support_size += 1
            transition[pair] += x
            for e in cycle_edges(C):
                loads[e] += x
        assert total == F(N, 2)
        assert loads == Counter({e: F(1) for e in graph_edges(G)})
        assert transition == Counter(M)
        if N >= 6:
            assert sum(w for e, w in M.items() if len(set(e) & {1, 2, 3}) == 1) == 0
        sizes.append((N+1, support_size))
    # A matching attaining the general lower bound r on new transitions.
    for r in range(1, 9):
        triples = [tuple(range(3*i, 3*i+3)) for i in range(2*r)]
        matching = [edge(T[1], T[2]) for T in triples]
        matching += [edge(triples[2*i][0], triples[2*i+1][0]) for i in range(r)]
        assert Counter(v for e in matching for v in e) == Counter(range(6*r))
        assert sum(u//3 != v//3 for u, v in matching) == r
    return {"complete_graph_support_sizes": sizes, "blossom_families_checked": 8}


# ---------- Petersen line graph and exact global-minimum gadget rings ----------

PETERSEN_HAMILTONS = [
    (0, 1, 2, 10, 14, 9, 13, 4, 12, 11, 8, 7, 5, 6, 3),
    (0, 1, 9, 7, 5, 3, 6, 14, 10, 2, 11, 8, 12, 13, 4),
    (0, 2, 1, 7, 9, 13, 14, 6, 10, 11, 12, 8, 5, 3, 4),
    (0, 2, 11, 10, 6, 5, 8, 7, 1, 9, 14, 13, 12, 4, 3),
]
PETERSEN_COMPLEMENT = (0, 2, 11, 10, 6, 14, 13, 12, 8, 5, 3, 4)
PETERSEN_TRIANGLE = (1, 7, 9)


def petersen_line():
    P = nx.petersen_graph()
    es = sorted(graph_edges(P))
    L = nx.line_graph(P)
    G = nx.relabel_nodes(L, {e: es.index(edge(*e)) for e in L})
    return P, G


def perfect_matchings(vertices):
    vertices = tuple(vertices)
    if not vertices:
        yield ()
        return
    a = vertices[0]
    for b in vertices[1:]:
        rest = tuple(v for v in vertices if v not in (a, b))
        for M in perfect_matchings(rest):
            yield (edge(a, b),)+M


def petersen_ring(t, H):
    assert t >= 2
    G = nx.Graph()
    for i in range(t):
        G.add_edges_from(((i, u), (i, v)) for u, v in H.edges())
        G.add_edge((i, 3), ((i+1) % t, 1))
        G.add_edge((i, 4), ((i+1) % t, 2))
    paths = {(C[1]-1, C[-1]-3): C[1:] for C in PETERSEN_HAMILTONS}
    assert set(paths) == set(product(range(2), repeat=2))
    A = tuple((i, v) for i in range(t) for v in paths[(0, 0)])
    B = tuple((i, v) for i in range(t) for v in PETERSEN_COMPLEMENT[1:])
    D = [A, B]+[tuple((i, v) for v in PETERSEN_TRIANGLE) for i in range(t)]
    forms = [1 if i % 2 == 0 else 2 for i in range(t)]
    if t % 2:
        forms[-1] = 3
    assert all(forms[i] != forms[(i+1) % t] for i in range(t))
    Hamiltons = []
    for seed in range(4):
        s = [(seed & z).bit_count() % 2 for z in forms]
        C = tuple((i, v) for i in range(t) for v in paths[(s[i-1], s[i])])
        Hamiltons.append(C)
    return G, D, Hamiltons, paths


def check_petersen():
    P, L = petersen_line()
    assert all(d == 4 for _, d in L.degree())
    PM = [M for M in perfect_matchings(range(10)) if set(M) <= graph_edges(P)]
    assert len(PM) == 6
    for M in PM:
        R = P.copy()
        R.remove_edges_from(M)
        assert sorted(len(S) for S in nx.connected_components(R)) == [5, 5]
    cycles = list(all_cycles(L))
    Hamiltons = [C for C in cycles if len(C) == 15]
    assert len(cycles) == 7514 and len(Hamiltons) == 160
    for C in Hamiltons:
        R = L.copy()
        R.remove_edges_from(cycle_edges(C))
        assert sorted(len(S) for S in nx.connected_components(R)) == [3, 12]
    cover = Counter(e for C in PETERSEN_HAMILTONS for e in cycle_edges(C))
    assert cover == Counter({e: 2 for e in graph_edges(L)})
    D = [PETERSEN_HAMILTONS[0], PETERSEN_COMPLEMENT, PETERSEN_TRIANGLE]
    assert_partition(L, D)
    assert_dual(L, cycles, {e: F(1, 15) for e in graph_edges(L)}, 2)
    uniform = {e: F(1, len(C)) for C in D for e in cycle_edges(C)}
    assert max(sum(uniform[e] for e in cycle_edges(C)) for C in cycles) == F(17, 10)
    H = L.copy()
    H.remove_node(0)
    cap_cases = Counter()
    hamilton14 = [C for C in cycles if len(C) == 14 and 0 not in C]
    assert len(hamilton14) == 52
    for C in hamilton14:
        R = H.copy()
        R.remove_edges_from(cycle_edges(C))
        components = list(nx.connected_components(R))
        if len(components) != 2 or any(all(R.degree[v] == 2 for v in S) for S in components):
            continue
        pairing = tuple(sorted(tuple(sorted(v for v in S if R.degree[v] == 1))
                               for S in components))
        cap_cases[pairing] += 1
    assert cap_cases == Counter({((1, 2), (3, 4)): 32})
    rows = []
    for t in (2, 3, 4, 5, 8, 12, 20, 40):
        G, D, HH, paths = petersen_ring(t, H)
        assert len(G) == 14*t and G.number_of_edges() == 28*t
        assert nx.is_connected(G) and all(d == 4 for _, d in G.degree())
        assert len(D) == t+2
        assert_partition(G, D)
        cover = Counter(e for C in HH for e in cycle_edges(C))
        assert all(len(C) == len(G) for C in HH)
        assert cover == Counter({e: 2 for e in graph_edges(G)})
        assert all(cycle_edges(C) & cycle_edges(D) for C, D in combinations(HH, 2))
        for C in HH:
            R = G.copy()
            R.remove_edges_from(cycle_edges(C))
            assert sorted(len(S) for S in nx.connected_components(R)) == [3]*t+[11*t]
        new_hamilton = tuple((i, v) for i in range(t) for v in paths[(1, 1)])
        uniform = {e: F(1, len(C)) for C in D for e in cycle_edges(C)}
        assert cycle_edges(new_hamilton) <= graph_edges(G)
        assert sum(uniform[e] for e in cycle_edges(new_hamilton)) == F(2*t, 3)+F(159, 154)
        rows.append({"t": t, "n": len(G), "cf": 2, "c_proved_in_note": t+2,
                     "gap": t, "residual_cycles_after_support_Hamilton": t+1})
    return {"base_cycles": len(cycles), "base_Hamiltons": len(Hamiltons),
            "punctured_Hamiltons": len(hamilton14), "cap_cases": 32, "rings": rows}


# ---------- Dense, pairwise-intersecting, near-optimal basic supports ----------

def check_dense_supports():
    rows = []
    for p in (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 101):
        beta = next(b for b in range(2, p) if len({pow(b, j, p) for j in range(p-1)}) == p-1)
        C = [tuple((c+pow(beta, j, p)) % p for j in range(p-1)) for c in range(p)]
        E = [cycle_edges(c) for c in C]
        cover = Counter(e for A in E for e in A)
        G = nx.complete_graph(p)
        assert cover == Counter({e: 2 for e in graph_edges(G)})
        assert all(len(E[i] & E[j]) == 1 for i in range(p) for j in range(i))
        inv = pow(1+beta, -1, p)
        for c, d in combinations(range(p), 2):
            e = edge(((d+beta*c)*inv) % p, ((c+beta*d)*inv) % p)
            assert E[c] & E[d] == {e}
        R = G.copy()
        R.remove_edges_from(E[0])
        assert min(dict(R.degree()).values()) == p-3
        assert all(d % 2 == 0 for _, d in R.degree())
        assert_partition(G, walecki((p-1)//2))
        rows.append((p, beta, p-3))
    return {"prime_beta_residual_min_degree": rows, "support_cost_excess": "1/2"}


# ---------- Exact two-edge-splice dual gluing and small exhaustive audit ----------

def check_splice():
    G1 = nx.complete_graph(5)
    D1 = walecki(2)
    y1 = {e: F(1, 5) for e in graph_edges(G1)}
    G2, _, D2, y2, _, _, _ = theta_chain(3, 3, 1)
    offset = len(G1)
    relabel = {v: v+offset for v in G2}
    G2 = nx.relabel_nodes(G2, relabel)
    D2 = [tuple(relabel[v] for v in C) for C in D2]
    y2 = {edge(relabel[u], relabel[v]): w for (u, v), w in y2.items()}
    e1, e2 = (0, 1), (offset, offset+3)
    C1 = next(C for C in D1 if e1 in cycle_edges(C))
    C2 = next(C for C in D2 if e2 in cycle_edges(C))

    def opened(C, e):
        R = nx.Graph(list(cycle_edges(C)-{e}))
        return tuple(nx.shortest_path(R, *e))

    cross = (edge(e1[0], e2[0]), edge(e1[1], e2[1]))
    G = nx.compose(G1, G2)
    G.remove_edges_from((e1, e2))
    G.add_edges_from(cross)
    D = [C for C in D1+D2 if C not in (C1, C2)]
    D.append(opened(C1, e1)+opened(C2, e2)[::-1])
    y = {e: w for e, w in {**y1, **y2}.items() if e not in (e1, e2)}
    for e in cross:
        y[e] = (y1[e1]+y2[e2]-1)/2
    assert_partition(G, D)
    cycles = list(all_cycles(G))
    assert_dual(G, cycles, y, len(D))
    assert len(D) == len(D1)+len(D2)-1 == 5
    return {"vertices": len(G), "all_cycles_checked": len(cycles), "c_and_cf": len(D)}


def is_series_parallel(G):
    H = G.copy()
    while H:
        v = min(H, key=lambda w: H.degree[w])
        nb = list(H[v])
        if len(nb) > 2:
            return False
        H.remove_node(v)
        if len(nb) == 2:
            H.add_edge(*nb)
    return True


def check_atlas():
    stats = Counter()
    for G in nx.graph_atlas_g():
        if not G or any(d % 2 for _, d in G.degree()):
            continue
        stats["all_even_nonzero_order"] += 1
        cycles = list(all_cycles(G))
        if not cycles:
            assert G.number_of_edges() == 0
            stats["edgeless"] += 1
            continue
        A, es = incidence(G, cycles)
        lp = linprog(np.ones(len(cycles)), A_eq=A, b_eq=np.ones(len(es)),
                     bounds=(0, None), method="highs")
        ip = milp(np.ones(len(cycles)), integrality=np.ones(len(cycles)),
                  bounds=Bounds(0, 1), constraints=LinearConstraint(A, 1, 1))
        assert lp.success and ip.success
        D = [C for C, z in zip(cycles, ip.x) if z > 0.5]
        y = {e: F(float(z)).limit_denominator(100000) for e, z in zip(es, lp.eqlin.marginals)}
        assert_partition(G, D)
        # Equality of an exact feasible dual and an exact partition proves optimality.
        assert_dual(G, cycles, y, len(D))
        stats["nonempty_SP" if is_series_parallel(G) else "nonempty_nonSP"] += 1
    assert stats == Counter(all_even_nonzero_order=84, edgeless=7,
                            nonempty_SP=45, nonempty_nonSP=32)
    return dict(stats)


def main():
    spec = Path(__file__).with_name("Spec.lean")
    assert sha256(spec.read_bytes()).hexdigest() == SPEC_SHA256
    results = {}
    for name, test in (("series_parallel", check_sp), ("theta_chains", check_theta_chains),
                       ("K5", check_k5), ("transition_extension", check_transition_extension),
                       ("Petersen", check_petersen), ("dense_supports", check_dense_supports),
                       ("two_edge_splice", check_splice), ("atlas", check_atlas)):
        results[name] = test()
        print(name + ": passed", flush=True)
    assert sha256(spec.read_bytes()).hexdigest() == SPEC_SHA256
    print(json.dumps(results, indent=2, sort_keys=True))
    print("All checks passed. Spec SHA-256 unchanged: " + SPEC_SHA256)


if __name__ == "__main__":
    main()
