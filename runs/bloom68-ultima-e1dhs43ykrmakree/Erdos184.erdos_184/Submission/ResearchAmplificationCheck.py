#!/usr/bin/env python3
"""Exact checks for ResearchAmplification.md; no random search or optimization solver.

Requires Python 3 and networkx. The infinite-family proofs are in the note.
All retained partitions are checked edge by edge, with simple cycles only.
No preexisting Submission file, including Spec.lean, is changed.
"""
from collections import Counter, defaultdict
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, product
from pathlib import Path
import json

import networkx as nx

SPEC_SHA256 = "429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde"


def edge(u, v):
    assert u != v
    return tuple(sorted((u, v), key=repr))


def graph_edges(G):
    return frozenset(edge(u, v) for u, v in G.edges())


def cycle_edges(C):
    C = tuple(C)
    assert len(C) >= 3 and len(C) == len(set(C))
    return frozenset(edge(u, v) for u, v in zip(C, C[1:] + C[:1]))


def path_edges(P):
    P = tuple(P)
    assert len(P) >= 2 and len(P) == len(set(P))
    return frozenset(edge(u, v) for u, v in zip(P, P[1:]))


def assert_partition(G, cycles, singletons=(), hamilton=False):
    used = Counter()
    for C in cycles:
        assert set(C) <= set(G)
        if hamilton:
            assert set(C) == set(G)
        used.update(cycle_edges(C))
    used.update(edge(*e) for e in singletons)
    assert used == Counter({e: 1 for e in graph_edges(G)})


def assert_double_cover(G, cycles, hamilton=False):
    used = Counter()
    for C in cycles:
        assert set(C) <= set(G)
        if hamilton:
            assert set(C) == set(G)
        used.update(cycle_edges(C))
    assert used == Counter({e: 2 for e in graph_edges(G)})


def blowup(G, s):
    assert s >= 1
    H = nx.Graph()
    H.add_nodes_from((v, a) for v in G for a in range(s))
    H.add_edges_from(((u, a), (v, b))
                     for u, v in G.edges() for a in range(s) for b in range(s))
    return H


def trace_two_regular(H):
    active = {v for v in H if H.degree(v)}
    assert all(H.degree(v) == 2 for v in active)
    cycles = []
    while active:
        start = min(active, key=repr)
        C, previous, current = [], None, start
        while True:
            assert current in active
            C.append(current)
            active.remove(current)
            options = [v for v in H[current] if v != previous]
            following = min(options, key=repr)
            if following == start:
                break
            previous, current = current, following
        cycle_edges(C)
        cycles.append(tuple(C))
    assert_partition(H, cycles)
    return cycles


# -------- Explicit path and cycle blow-up factorizations --------


def path_two_blowup(P):
    """One C4 for an edge; two cycles of length 2k for a k-edge path, k>=2."""
    P = tuple(P)
    k = len(P) - 1
    assert k >= 1 and len(set(P)) == k + 1
    if k == 1:
        return [((P[0], 0), (P[1], 0), (P[0], 1), (P[1], 1))]
    cycles = []
    for h in range(2):
        H = nx.Graph()
        H.add_edges_from(((P[0], h), (P[1], a)) for a in range(2))
        H.add_edges_from(((P[-1], h), (P[-2], a)) for a in range(2))
        for i in range(1, k - 1):
            H.add_edges_from(((P[i], a), (P[i+1], a ^ h)) for a in range(2))
        D = trace_two_regular(H)
        assert len(D) == 1 and len(D[0]) == 2*k
        cycles += D
    return cycles


def cycle_two_blowup(C):
    """Two Hamilton cycles, using opposite stars at one base vertex."""
    C = tuple(C)
    cycle_edges(C)
    outside_path = C[2:] + C[:1]
    cycles = []
    for h in range(2):
        H = nx.Graph()
        H.add_edges_from(((C[1], h), (C[0], a)) for a in range(2))
        H.add_edges_from(((C[1], 1-h), (C[2], a)) for a in range(2))
        for u, v in zip(outside_path, outside_path[1:]):
            H.add_edges_from(((u, a), (v, a ^ h)) for a in range(2))
        D = trace_two_regular(H)
        assert len(D) == 1 and len(D[0]) == 2*len(C)
        cycles += D
    return cycles


def shift_cycle_blowup(C, s):
    """Hamilton decomposition if base cycle length is even or s is odd."""
    C = tuple(C)
    ell = len(C)
    assert ell >= 3 and s >= 1 and (ell % 2 == 0 or s % 2 == 1)
    cycles = []
    for j in range(s):
        if ell % 2 == 0:
            shifts = [j if i % 2 == 0 else -j for i in range(ell)]
            shifts[0] += 1
        else:
            shifts = [j, j, 1-2*j]
            shifts += [j if i % 2 == 0 else -j for i in range(ell-3)]
        assert sum(shifts) % s == 1 % s
        H = nx.Graph()
        for i, u in enumerate(C):
            v = C[(i+1) % ell]
            H.add_edges_from(((u, a), (v, (a+shifts[i]) % s)) for a in range(s))
        D = trace_two_regular(H)
        assert len(D) == 1 and len(D[0]) == ell*s
        cycles += D
    return cycles


def cycle_blowup(C, s):
    """Exactly s Hamilton cycles for C[s], for every ell>=3 and s>=1."""
    if len(C) % 2 == 0 or s % 2:
        return shift_cycle_blowup(C, s)
    half = s // 2
    result = []
    for H in cycle_two_blowup(C):
        for Q in shift_cycle_blowup(H, half):
            result.append(tuple((v, b*half+a) for (v, b), a in Q))
    return result


def check_blowup_templates():
    path_cases = 0
    for k in range(1, 151):
        G = nx.path_graph(k+1)
        D = path_two_blowup(tuple(range(k+1)))
        assert len(D) == (1 if k == 1 else 2)
        assert_partition(blowup(G, 2), D)
        path_cases += 1
    cycle_cases = 0
    for ell in range(3, 31):
        G = nx.cycle_graph(ell)
        C = tuple(range(ell))
        assert_partition(blowup(G, 2), cycle_two_blowup(C), hamilton=True)
        for s in range(1, 21):
            D = cycle_blowup(C, s)
            assert len(D) == s
            assert_partition(blowup(G, s), D, hamilton=True)
            cycle_cases += 1
    return {"path_templates": path_cases, "cycle_templates": cycle_cases}


# -------- Exact binary phase / parity-orientation theorem --------


def optimal_parity_orientation(q, edges):
    """Orient a loopless multigraph, minimizing vertices of even indegree.

    Return the head of each labelled edge and component data. Isolated vertices
    are allowed here, although they do not occur in a cycle-cover multigraph.
    """
    edges = list(edges)
    adjacency = [[] for _ in range(q)]
    for j, (u, v) in enumerate(edges):
        assert 0 <= u < q and 0 <= v < q and u != v
        adjacency[u].append((v, j))
        adjacency[v].append((u, j))
    seen, components = set(), []
    parent, parent_edge, orders = {}, {}, []
    for root in range(q):
        if root in seen:
            continue
        order = [root]
        seen.add(root)
        for u in order:
            for v, e in adjacency[u]:
                if v not in seen:
                    seen.add(v)
                    parent[v], parent_edge[v] = u, e
                    order.append(v)
        components.append(set(order))
        orders.append(order)
    target = [1]*q
    data = []
    for S in components:
        m = sum(1 for u, v in edges if u in S)
        defect = (m-len(S)) % 2
        if defect:
            target[min(S)] = 0
        data.append({"vertices": len(S), "edges": m, "defect": defect})
    tree_edges = set(parent_edge.values())
    heads, parity = {}, [0]*q
    for j, (u, v) in enumerate(edges):
        if j not in tree_edges:
            heads[j] = v
            parity[v] ^= 1
    for order in orders:
        for v in reversed(order[1:]):
            e, u = parent_edge[v], parent[v]
            head = v if parity[v] != target[v] else u
            heads[e] = head
            parity[head] ^= 1
        root = order[0]
        assert parity[root] == target[root]
    assert len(heads) == len(edges)
    assert parity == target
    epsilon = sum(d["defect"] for d in data)
    assert parity.count(0) == epsilon
    return [heads[j] for j in range(len(edges))], data


def check_parity_orientations():
    cases, orientations = 0, 0
    for q in range(1, 5):
        pairs = list(combinations(range(q), 2))
        for multiplicities in product(range(3), repeat=len(pairs)):
            es = [e for e, m in zip(pairs, multiplicities) for _ in range(m)]
            heads, data = optimal_parity_orientation(q, es)
            predicted = sum(d["defect"] for d in data)
            best = q
            for choices in product(range(2), repeat=len(es)):
                parity = [0]*q
                for e, choice in zip(es, choices):
                    parity[e[choice]] ^= 1
                best = min(best, parity.count(0))
                orientations += 1
            assert best == predicted
            cases += 1
    return {"multigraphs": cases, "all_orientations_checked": orientations}


def lift_double_cover(G, cover):
    assert_double_cover(G, cover)
    occurrences = defaultdict(list)
    for i, C in enumerate(cover):
        for e in cycle_edges(C):
            occurrences[e].append(i)
    labelled_edges = sorted(occurrences, key=repr)
    pairs = [tuple(occurrences[e]) for e in labelled_edges]
    heads, data = optimal_parity_orientation(len(cover), pairs)
    crossed = dict(zip(labelled_edges, heads))
    cycles = []
    for i, C in enumerate(cover):
        H = nx.Graph()
        for e in cycle_edges(C):
            u, v = e
            bit = int(crossed[e] == i)
            H.add_edges_from(((u, a), (v, a ^ bit)) for a in range(2))
        D = trace_two_regular(H)
        parity = sum(crossed[e] == i for e in cycle_edges(C)) % 2
        assert len(D) == (1 if parity else 2)
        cycles += D
    epsilon = sum(d["defect"] for d in data)
    assert len(cycles) == len(cover) + epsilon
    assert_partition(blowup(G, 2), cycles)
    return cycles, data


def check_lift_scope_warning():
    rows = []
    for ell in range(3, 20):
        G, C = nx.cycle_graph(ell), tuple(range(ell))
        lifted, data = lift_double_cover(G, [C, C])
        assert len(lifted) == 2 + ell % 2
        unrestricted = cycle_two_blowup(C)
        assert_partition(blowup(G, 2), unrestricted, hamilton=True)
        assert len(unrestricted) == 2  # Degree-four lower bound proves optimality.
        rows.append({"base_cycle_length": ell, "restricted_lift_minimum": len(lifted),
                     "actual_minimum": 2})
    # A non-Eulerian base is permitted in the lifting theorem.
    G = nx.complete_graph(4)
    cover = [(0, 1, 2, 3), (0, 1, 3, 2), (0, 2, 1, 3)]
    lifted, data = lift_double_cover(G, cover)
    assert len(lifted) == 4 and sum(d["defect"] for d in data) == 1
    return {"odd_cycle_warning": rows, "K4_three_cycle_double_cover_lift_cost": 4}


# -------- The supplied Petersen rings and their exact gap collapse --------

PETERSEN_EDGES = [(0, 1), (0, 4), (0, 5), (1, 2), (1, 6), (2, 3), (2, 7),
                  (3, 4), (3, 8), (4, 9), (5, 7), (5, 8), (6, 8), (6, 9), (7, 9)]
PETERSEN_HAMILTONS = [
    (0, 1, 2, 10, 14, 9, 13, 4, 12, 11, 8, 7, 5, 6, 3),
    (0, 1, 9, 7, 5, 3, 6, 14, 10, 2, 11, 8, 12, 13, 4),
    (0, 2, 1, 7, 9, 13, 14, 6, 10, 11, 12, 8, 5, 3, 4),
    (0, 2, 11, 10, 6, 5, 8, 7, 1, 9, 14, 13, 12, 4, 3),
]
PETERSEN_COMPLEMENT = (0, 2, 11, 10, 6, 14, 13, 12, 8, 5, 3, 4)


def petersen_ring(t):
    assert t >= 2
    L = nx.Graph()
    L.add_nodes_from(range(15))
    L.add_edges_from((i, j) for i, j in combinations(range(15), 2)
                     if set(PETERSEN_EDGES[i]) & set(PETERSEN_EDGES[j]))
    assert_double_cover(L, PETERSEN_HAMILTONS, hamilton=True)
    H = L.copy()
    H.remove_node(0)
    G = nx.Graph()
    for i in range(t):
        G.add_edges_from(((i, u), (i, v)) for u, v in H.edges())
        G.add_edge((i, 3), ((i+1) % t, 1))
        G.add_edge((i, 4), ((i+1) % t, 2))
    paths = {(C[1]-1, C[-1]-3): C[1:] for C in PETERSEN_HAMILTONS}
    assert set(paths) == set(product(range(2), repeat=2))
    old = [tuple((i, v) for i in range(t) for v in paths[(0, 0)]),
           tuple((i, v) for i in range(t) for v in PETERSEN_COMPLEMENT[1:])]
    old += [tuple((i, v) for v in (1, 7, 9)) for i in range(t)]
    assert_partition(G, old)
    forms = [1 if i % 2 == 0 else 2 for i in range(t)]
    if t % 2:
        forms[-1] = 3
    assert all(forms[i] != forms[(i+1) % t] for i in range(t))
    cover = []
    for seed in range(4):
        bits = [(seed & f).bit_count() % 2 for f in forms]
        cover.append(tuple((i, v) for i in range(t)
                           for v in paths[(bits[i-1], bits[i])]))
    assert len(G) == 14*t and G.number_of_edges() == 28*t
    assert all(d == 4 for _, d in G.degree())
    assert_double_cover(G, cover, hamilton=True)
    return G, cover


def check_petersen_collapse():
    rows = []
    for t in (2, 3, 4, 5, 8, 12, 20, 40, 101):
        G, cover = petersen_ring(t)
        doubled, data = lift_double_cover(G, cover)
        assert len(doubled) == 4
        assert all(d["defect"] == 0 for d in data)
        assert_partition(blowup(G, 2), doubled, hamilton=True)
        for s in (1, 2, 3, 5):
            cycles = []
            for H in doubled:
                for C in cycle_blowup(H, s):
                    cycles.append(tuple((v, b*s+a) for (v, b), a in C))
            B = blowup(G, 2*s)
            assert len(B) == 28*t*s and B.number_of_edges() == 112*t*s*s
            assert len(cycles) == 4*s
            assert all(d == 8*s for _, d in B.degree())
            assert_partition(B, cycles, hamilton=True)
            # A vertex supplies a lower bound 8s/2 for ALL partitions and the LP.
            assert B.degree(next(iter(B))) // 2 == len(cycles)
            rows.append({"t": t, "clone_factor": 2*s, "n": len(B),
                         "c_and_cf": len(cycles), "gap": 0})
    return rows


# -------- Lovasz paired-twin consequence, checked on all small graphs --------


def all_cycles(G):
    """One representative per undirected simple cycle, integer vertices."""
    for start in sorted(G):
        def visit(P, used):
            for v in sorted(G[P[-1]]):
                if v == start and len(P) >= 3 and P[1] < P[-1]:
                    yield tuple(P)
                elif v > start and v not in used:
                    yield from visit(P + [v], used | {v})
        yield from visit([start], {start})


def all_paths(G):
    for start in sorted(G):
        def visit(P, used):
            if len(P) >= 2 and P[0] < P[-1]:
                yield tuple(P)
            for v in sorted(G[P[-1]]):
                if v not in used:
                    yield from visit(P + [v], used | {v})
        yield from visit([start], {start})


def small_partition(G, kind, budget=None):
    """Exact finite all-column DP, only used for verification at order <=6."""
    es = sorted(graph_edges(G), key=repr)
    ids = {e: i for i, e in enumerate(es)}
    pieces = [("C", C) for C in all_cycles(G)]
    if kind == "paths_cycles":
        pieces += [("P", P) for P in all_paths(G)]
    elif kind == "cycles_edges":
        pieces += [("P", e) for e in es]
    masks = []
    for typ, P in pieces:
        E = cycle_edges(P) if typ == "C" else path_edges(P)
        masks.append(sum(1 << ids[e] for e in E))
    by_edge = [[] for _ in es]
    for j, mask in enumerate(masks):
        for i in range(len(es)):
            if mask >> i & 1:
                by_edge[i].append(j)
    for opts in by_edge:
        opts.sort(key=lambda j: (-masks[j].bit_count(), j))
    maximum = max((m.bit_count() for m in masks), default=1)

    @lru_cache(None)
    def solve(mask, k):
        if not mask:
            return ()
        if k <= 0 or mask.bit_count() > k*maximum:
            return None
        first = (mask & -mask).bit_length()-1
        for j in by_edge[first]:
            if masks[j] & mask == masks[j]:
                rest = solve(mask ^ masks[j], k-1)
                if rest is not None:
                    return (j,) + rest
        return None

    if budget is None:
        budgets = range(len(es)+1)
    else:
        budgets = [budget]
    full = (1 << len(es))-1
    for k in budgets:
        result = solve(full, k)
        if result is not None:
            return [pieces[j] for j in result]
    return None


def check_small_graphs():
    twin_cases = even_cases = lift_cases = uniform_cases = 0
    for G in nx.graph_atlas_g():
        if len(G) > 6:
            continue
        pieces = small_partition(G, "paths_cycles", len(G)//2)
        assert pieces is not None
        cycles = []
        for typ, P in pieces:
            cycles += cycle_two_blowup(P) if typ == "C" else path_two_blowup(P)
        assert len(cycles) <= 2*(len(G)//2) <= len(G)
        assert_partition(blowup(G, 2), cycles)
        twin_cases += 1
        if not all(d % 2 == 0 for _, d in G.degree()):
            continue
        pure = small_partition(G, "cycles")
        mixed = small_partition(G, "cycles_edges")
        assert pure is not None and len(pure) == len(mixed)
        assert all(typ == "C" for typ, P in pure)
        D = [P for typ, P in pure]
        assert_partition(G, D)
        lifted, data = lift_double_cover(G, D + D)
        lift_cases += 1
        for s in (1, 2, 3, 4, 5):
            output = [C for H in D for C in cycle_blowup(H, s)]
            assert len(output) == s*len(D)
            assert_partition(blowup(G, s), output)
            uniform_cases += 1
        even_cases += 1
    return {"all_graphs_up_to_6": twin_cases, "even_graphs_p_equals_c": even_cases,
            "cycle_cover_lifts": lift_cases, "uniform_partition_lifts": uniform_cases}


# -------- Global Cartesian regrouping of uniform cycle factors --------


def cartesian_power(G, k):
    assert k >= 1
    vertices = tuple(G)
    H = nx.Graph()
    H.add_nodes_from(product(vertices, repeat=k))
    for coordinate in range(k):
        for background in product(vertices, repeat=k-1):
            for u, v in G.edges():
                x, y = list(background), list(background)
                x.insert(coordinate, u)
                y.insert(coordinate, v)
                H.add_edge(tuple(x), tuple(y))
    assert len(H) == len(G)**k
    assert H.number_of_edges() == k*G.number_of_edges()*len(G)**(k-1)
    return H


def torus_hamilton_cycles(m, ell):
    """Two Hamilton cycles in C_m square C_ell, under the proved arithmetic condition."""
    from math import gcd
    assert ell >= 3 and m >= 3 and m % ell == 0 and gcd(m, ell-1) == 1
    result = []
    for colour in range(2):
        x = y = 0
        C, visited = [], set()
        while (x, y) not in visited:
            visited.add((x, y))
            C.append((x, y))
            horizontal = ((x+y) % ell != ell-1) ^ bool(colour)
            if horizontal:
                x = (x+1) % m
            else:
                y = (y+1) % ell
        assert (x, y) == (0, 0) and len(C) == m*ell
        result.append(tuple(C))
    return tuple(result)


@lru_cache(None)
def cycle_power_partition(ell, k):
    """A partition of C_ell^square k, retaining a distinguished Hamilton cycle."""
    assert ell >= 3 and k >= 1
    if k == 1:
        return (tuple((v,) for v in range(ell)),)
    previous = cycle_power_partition(ell, k-1)
    distinguished = previous[0]
    m = len(distinguished)
    assert m == ell**(k-1)
    result = [tuple(distinguished[x] + (y,) for x, y in C)
              for C in torus_hamilton_cycles(m, ell)]
    result += [tuple(v + (y,) for v in C)
               for C in previous[1:] for y in range(ell)]
    assert len(result) == (ell**(k-1) + ell-2)//(ell-1)
    assert len(result[0]) == ell**k
    return tuple(result)


def partial_cycle_factor_power(vertices, cycles, k):
    """Cartesian power of b vertex-disjoint ell-cycles plus a isolated vertices."""
    vertices, cycles = tuple(vertices), tuple(tuple(C) for C in cycles)
    assert k >= 1 and cycles
    ell, b = len(cycles[0]), len(cycles)
    assert all(len(C) == ell for C in cycles)
    assert len(set(v for C in cycles for v in C)) == b*ell
    active_vertices = {v for C in cycles for v in C}
    assert active_vertices <= set(vertices)
    isolates = tuple(v for v in vertices if v not in active_vertices)
    a, n = len(isolates), len(vertices)
    output = []
    for j in range(1, k+1):
        template = cycle_power_partition(ell, j)
        for active in combinations(range(k), j):
            outside = tuple(i for i in range(k) if i not in active)
            for background in product(isolates, repeat=k-j):
                fixed = dict(zip(outside, background))
                for component_cycles in product(range(b), repeat=j):
                    for C in template:
                        replacement = []
                        for point in C:
                            vertex = [None]*k
                            for i in outside:
                                vertex[i] = fixed[i]
                            for i, cycle_id, value in zip(active, component_cycles, point):
                                vertex[i] = cycles[cycle_id][value]
                            replacement.append(tuple(vertex))
                        output.append(tuple(replacement))
    numerator = n**k + ell*(ell-2)*(a+b)**k - (ell-1)**2*a**k
    expected, remainder = divmod(numerator, ell*(ell-1))
    assert remainder == 0 and len(output) == expected
    assert ell*len(output) <= n**k - a**k
    return output


def check_cartesian_repair():
    torus_cases = cube_cases = factor_cases = 0
    for ell in range(3, 10):
        for exponent in range(1, 4):
            m = ell**exponent
            G = nx.cartesian_product(nx.cycle_graph(m), nx.cycle_graph(ell))
            D = torus_hamilton_cycles(m, ell)
            assert len(D) == 2
            assert_partition(G, D, hamilton=True)
            torus_cases += 1
    for ell in range(3, 9):
        for k in range(1, 5):
            G = cartesian_power(nx.cycle_graph(ell), k)
            D = cycle_power_partition(ell, k)
            assert set(D[0]) == set(G)
            assert len(D) == (ell**(k-1)+ell-2)//(ell-1)
            assert_partition(G, D)
            cube_cases += 1
    for ell, b, a, max_k in [(3, 1, 11, 3), (3, 2, 1, 4), (4, 2, 1, 3),
                              (5, 1, 2, 3), (6, 1, 0, 4)]:
        F = nx.Graph()
        F.add_nodes_from(range(a+b*ell))
        cycles = [tuple(range(i*ell, (i+1)*ell)) for i in range(b)]
        F.add_edges_from(e for C in cycles for e in cycle_edges(C))
        for k in range(1, max_k+1):
            output = partial_cycle_factor_power(tuple(F), cycles, k)
            assert_partition(cartesian_power(F, k), output)
            factor_cases += 1
    rows = []
    for t, k in [(2, 1), (2, 2), (2, 3), (3, 2), (5, 2)]:
        G, unused_cover = petersen_ring(t)
        paths = {(C[1]-1, C[-1]-3): C[1:] for C in PETERSEN_HAMILTONS}
        first = tuple((i, v) for i in range(t) for v in paths[(0, 0)])
        second = tuple((i, v) for i in range(t) for v in PETERSEN_COMPLEMENT[1:])
        triangles = [tuple((i, v) for v in (1, 7, 9)) for i in range(t)]
        assert_partition(G, [first, second] + triangles)
        output = []
        for factor in ([first], [second], triangles):
            output += partial_cycle_factor_power(tuple(G), factor, k)
        target = cartesian_power(G, k)
        assert_partition(target, output)
        assert 12*len(output) < 5*len(target)
        rows.append({"ring_t": t, "cartesian_exponent": k, "n": len(target),
                     "constructed_count_NOT_claimed_minimum": len(output)})
    return {"two_Hamilton_tori": torus_cases, "cycle_power_partitions": cube_cases,
            "partial_factor_power_partitions": factor_cases, "Petersen_cartesian_powers": rows}


# -------- Nonuniform twin fibres and fully shared Petersen layers --------


def variable_blowup(G, sizes):
    H = nx.Graph()
    H.add_nodes_from((v, a) for v in G for a in range(sizes[v]))
    H.add_edges_from(((u, a), (v, b)) for u, v in G.edges()
                     for a in range(sizes[u]) for b in range(sizes[v]))
    return H


def check_nonuniform_twins():
    cases = 0
    bases = [nx.path_graph(2), nx.path_graph(3), nx.cycle_graph(3), nx.cycle_graph(4)]
    for base in bases:
        for choice in product((1, 2, 3), repeat=len(base)):
            if sum(choice) > 6:
                continue
            sizes = dict(zip(base, choice))
            quotient = variable_blowup(base, sizes)
            labels = sorted(quotient)
            integers = nx.relabel_nodes(quotient, {v: i for i, v in enumerate(labels)})
            old = small_partition(integers, "paths_cycles", len(integers)//2)
            assert old is not None
            cycles = []
            for kind, piece in old:
                lifted = cycle_two_blowup(piece) if kind == "C" else path_two_blowup(piece)
                for C in lifted:
                    cycles.append(tuple((labels[i][0], 2*labels[i][1]+b) for i, b in C))
            target = variable_blowup(base, {v: 2*a for v, a in sizes.items()})
            assert len(cycles) <= len(target)//2
            assert_partition(target, cycles)
            cases += 1
    return {"nonuniform_even_fibre_instances": cases}


def shared_petersen_overlay(k):
    """k genuine R_(14^(k-1)) layers on exactly the same 14^k old vertices."""
    assert k >= 2
    T = 14**(k-1)
    R, base_cover = petersen_ring(T)
    paths = {(C[1]-1, C[-1]-3): C[1:] for C in PETERSEN_HAMILTONS}
    base_old = [tuple((i, v) for i in range(T) for v in paths[(0, 0)]),
                tuple((i, v) for i in range(T) for v in PETERSEN_COMPLEMENT[1:])]
    base_old += [tuple((i, v) for v in (1, 7, 9)) for i in range(T)]
    assert_partition(R, base_old)
    G, cover, old = nx.Graph(), [], []
    for coordinate in range(k):
        mapping = {}
        for block, v in R:
            digits = [0]*(k-1)
            number = block
            for j in range(k-2, -1, -1):
                digits[j], number = number % 14, number // 14
            assert number == 0
            digits.insert(coordinate, v-1)
            mapping[(block, v)] = tuple(digits)
        assert len(set(mapping.values())) == 14**k
        new_edges = {edge(mapping[u], mapping[v]) for u, v in R.edges()}
        assert not (new_edges & graph_edges(G))
        G.add_edges_from(new_edges)
        cover += [tuple(mapping[v] for v in C) for C in base_cover]
        old += [tuple(mapping[v] for v in C) for C in base_old]
    assert len(G) == 14**k and G.number_of_edges() == 2*k*14**k
    assert all(d == 4*k for _, d in G.degree())
    assert len(cover) == 4*k and len(old) == k*(T+2)
    assert_double_cover(G, cover, hamilton=True)
    assert_partition(G, old)
    for coordinate in range(k):
        fibre = set()
        for value in range(14):
            vertex = [0]*k
            vertex[coordinate] = value
            fibre.add(tuple(vertex))
        boundary = sum((u in fibre) != (v in fibre) for u, v in G.edges())
        assert boundary == 4 + 56*(k-1)
    return G, cover, old


def check_shared_petersen_layers():
    rows = []
    for k in (2, 3):
        G, cover, old = shared_petersen_overlay(k)
        retained = [C for C in old if len(C) > 3]
        assert len(retained) == 2*k
        triangle_grid = nx.Graph()
        triangle_grid.add_nodes_from(range(14))
        triangle_grid.add_edges_from(cycle_edges((0, 6, 8)))
        residual_edges = set(e for C in old if len(C) == 3 for e in cycle_edges(C))
        assert graph_edges(cartesian_power(triangle_grid, k)) == residual_edges
        repaired = retained + partial_cycle_factor_power(range(14), [(0, 6, 8)], k)
        numerator = 14**k + 3*12**k - 4*11**k
        assert numerator % 6 == 0
        assert len(repaired) == 2*k + numerator//6
        assert 3*len(repaired) <= len(G)
        assert_partition(G, repaired)
        doubled, data = lift_double_cover(G, cover)
        assert len(doubled) == 4*k
        assert all(d["defect"] == 0 for d in data)
        assert_partition(blowup(G, 2), doubled, hamilton=True)
        for s in ((1, 2, 3) if k == 2 else (1, 2)):
            output = []
            for H in doubled:
                for C in cycle_blowup(H, s):
                    output.append(tuple((v, b*s+a) for (v, b), a in C))
            target = blowup(G, 2*s)
            assert len(output) == 4*k*s
            assert all(d == 8*k*s for _, d in target.degree())
            assert_partition(target, output, hamilton=True)
            rows.append({"genuine_Petersen_layers": k, "old_order": len(G),
                         "old_fractional_optimum": 2*k,
                         "old_supplied_partition_NOT_claimed_minimum": len(old),
                         "uncloned_global_repair_count_NOT_claimed_minimum": len(repaired),
                         "old_fibre_boundary": 4+56*(k-1),
                         "clone_factor": 2*s, "new_order": len(target),
                         "new_c_and_cf": 4*k*s})
    return rows


# -------- Walecki and complete local transition libraries (line graphs) --------


def clique_partition(vertices, prescribed_matching=None):
    """Hamilton cycles of K_d (odd d), or K_d-M and matching M (even d)."""
    vertices = list(vertices)
    n, raw = len(vertices), []
    if n <= 1:
        assert not prescribed_matching
        return [], []
    if n % 2:
        k = (n-1)//2
        for t in range(k):
            C = [2*k, t]
            for j in range(1, k):
                C.extend(((t-j) % (2*k), (t+j) % (2*k)))
            C.append((t-k) % (2*k))
            raw.append(tuple(C))
    else:
        k, modulus = n//2, n-1
        for t in range(k-1):
            C = [n-1, t]
            for j in range(1, k):
                C.extend(((t-j) % modulus, (t+j) % modulus))
            raw.append(tuple(C))
    used = Counter(e for C in raw for e in cycle_edges(C))
    assert all(count == 1 for count in used.values())
    leftover = sorted(graph_edges(nx.complete_graph(n)) - set(used), key=repr)
    if n % 2:
        assert not leftover and prescribed_matching is None
    else:
        assert len(leftover) == n//2
        assert Counter(v for e in leftover for v in e) == Counter(range(n))
    mapping = dict(enumerate(vertices))
    if prescribed_matching is not None:
        target = sorted([edge(*e) for e in prescribed_matching], key=repr)
        assert Counter(v for e in target for v in e) == Counter(vertices)
        assert len(target) == len(leftover)
        mapping = {}
        for (a, b), (u, v) in zip(leftover, target):
            mapping[a], mapping[b] = u, v
    cycles = [tuple(mapping[v] for v in C) for C in raw]
    matching = [edge(mapping[u], mapping[v]) for u, v in leftover]
    K = nx.complete_graph(vertices)
    assert_partition(K, cycles, matching)
    if prescribed_matching is not None:
        assert set(matching) == set(edge(*e) for e in prescribed_matching)
    return cycles, matching


def make_line_graph(X):
    G = nx.Graph()
    G.add_nodes_from(graph_edges(X))
    for v in X:
        incident = [edge(v, u) for u in X[v]]
        G.add_edges_from(combinations(incident, 2))
    return G


def line_partition(X, pure):
    G = make_line_graph(X)
    cycles, singletons, formula = [], [], 0
    if not pure:
        for v in X:
            incident = sorted([edge(v, u) for u in X[v]], key=repr)
            C, M = clique_partition(incident)
            cycles += C
            singletons += M
        assert_partition(G, cycles, singletons)
        h = sum(X.degree(v) > 0 for v in X)
        assert len(cycles) + len(singletons) <= 2*len(G) - h
        return cycles, singletons
    assert all(d % 2 == 0 for _, d in G.degree())
    for S in nx.connected_components(X):
        Y = X.subgraph(S)
        m, h = Y.number_of_edges(), len(Y)
        if m == 0:
            continue
        parities = {d % 2 for _, d in Y.degree()}
        assert len(parities) == 1
        if parities == {1}:
            formula += m-h//2
            for v in Y:
                incident = sorted([edge(v, u) for u in Y[v]], key=repr)
                C, M = clique_partition(incident)
                assert not M
                cycles += C
        else:
            formula += m-h+1
            tour = tuple(edge(u, v) for u, v in nx.eulerian_circuit(Y))
            cycle_edges(tour)
            assert set(tour) == graph_edges(Y)
            cycles.append(tour)
            transitions = defaultdict(list)
            for e, f in zip(tour, tour[1:] + tour[:1]):
                common = set(e) & set(f)
                assert len(common) == 1
                transitions[next(iter(common))].append(edge(e, f))
            for v in Y:
                incident = sorted([edge(v, u) for u in Y[v]], key=repr)
                C, M = clique_partition(incident, transitions[v])
                cycles += C
    assert len(cycles) == formula
    assert_partition(G, cycles)
    assert len(cycles) <= len(G) - nx.number_connected_components(G)
    return cycles, singletons


def check_line_graphs():
    all_cases = even_cases = 0
    for X in nx.graph_atlas_g():
        line_partition(X, pure=False)
        all_cases += 1
        G = make_line_graph(X)
        if all(d % 2 == 0 for _, d in G.degree()):
            line_partition(X, pure=True)
            even_cases += 1
    for n in range(1, 42):
        clique_partition(range(n))
    sharp_rows = []
    for h in (3, 5, 7, 9, 15, 25, 41):
        G = nx.complete_graph(h)
        D, M = clique_partition(range(h))
        assert not M
        lifted = [Q for C in D for Q in cycle_two_blowup(C)]
        assert_partition(blowup(G, 2), lifted, hamilton=True)
        assert len(lifted) == h-1
        sharp_rows.append({"order": 2*h, "minimum": h-1})
    iterations = []
    X = nx.Graph(PETERSEN_EDGES)
    for step in range(1, 5):
        G = make_line_graph(X)
        D, unused = line_partition(X, pure=True)
        iterations.append({"iteration": step, "n": len(G), "degree": G.degree(next(iter(G))),
                           "constructed_count_not_claimed_optimal": len(D)})
        # Relabelling keeps nested edge labels from growing exponentially.
        X = nx.convert_node_labels_to_integers(G)
    return {"all_hosts_up_to_7": all_cases, "Eulerian_line_graphs": even_cases,
            "clique_orders": 41, "paired_twin_asymptotic_sharpness": sharp_rows,
            "iterated_line_graphs": iterations}


def main():
    directory = Path(__file__).resolve().parent
    protected = {p.name: sha256(p.read_bytes()).hexdigest() for p in directory.iterdir()
                 if p.is_file() and not p.name.startswith("ResearchAmplification")}
    assert protected["Spec.lean"] == SPEC_SHA256
    results = {}
    for name, check in [
        ("blowup_templates", check_blowup_templates),
        ("parity_orientation_exhaustive", check_parity_orientations),
        ("scope_warning", check_lift_scope_warning),
        ("small_graph_exact_checks", check_small_graphs),
        ("cartesian_global_repair", check_cartesian_repair),
        ("nonuniform_even_twins", check_nonuniform_twins),
        ("Petersen_even_clone_collapse", check_petersen_collapse),
        ("fully_shared_Petersen_layers", check_shared_petersen_layers),
        ("complete_transition_libraries", check_line_graphs),
    ]:
        results[name] = check()
        print("PASS", name, flush=True)
    for name, expected in protected.items():
        assert sha256((directory/name).read_bytes()).hexdigest() == expected
    results["protected_preexisting_files"] = len(protected)
    results["Spec_sha256"] = SPEC_SHA256
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
