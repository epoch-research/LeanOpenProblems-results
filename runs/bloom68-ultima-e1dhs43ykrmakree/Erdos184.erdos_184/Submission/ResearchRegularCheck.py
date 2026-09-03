#!/usr/bin/env python3
"""Exact checks for ResearchRegular.md; no numerical LP/MILP is used.

Dependencies: NetworkX and SymPy. Run from any working directory.
This file reads, but never writes, the specification or existing research files.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
import hashlib
import random

import networkx as nx
import sympy as sp

SPEC_SHA256 = "429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde"
HERE = Path(__file__).resolve().parent


def check_spec():
    assert hashlib.sha256((HERE / "Spec.lean").read_bytes()).hexdigest() == SPEC_SHA256


def edge(u, v):
    return tuple(sorted((u, v)))


def cycle_edges(c):
    assert len(c) >= 3 and len(set(c)) == len(c)
    return {edge(u, v) for u, v in zip(c, c[1:] + c[:1])}


def all_simple_cycles(g):
    """Independent undirected DFS, not closed-trail enumeration."""
    answer = []
    for root in sorted(g):
        def dfs(path, seen):
            for v in sorted(g[path[-1]]):
                if v == root and len(path) >= 3:
                    if path[1] < path[-1]:
                        answer.append(tuple(path))
                elif v > root and v not in seen:
                    dfs(path + [v], seen | {v})
        dfs([root], {root})
    assert len({frozenset(cycle_edges(c)) for c in answer}) == len(answer)
    return answer


def as_mask(edges, order):
    index = {e: i for i, e in enumerate(order)}
    return sum(1 << index[e] for e in edges)


def bits(mask, m):
    return [i for i in range(m) if mask >> i & 1]


def check_partition(masks, m):
    used = 0
    for mask in masks:
        assert mask and not (mask & used)
        used |= mask
    assert used == (1 << m) - 1


def exact_min_partition(circuits, m):
    by_edge = [[c for c in circuits if c >> e & 1] for e in range(m)]
    memo = {0: ()}

    def solve(rem):
        if rem in memo:
            return memo[rem]
        e = (rem & -rem).bit_length() - 1
        best = None
        for c in by_edge[e]:
            if c & rem == c:
                tail = solve(rem ^ c)
                if tail is not None and (best is None or len(tail) + 1 < len(best)):
                    best = (c,) + tail
        memo[rem] = best
        return best
    return solve((1 << m) - 1)


def check_petersen_hole():
    p = nx.petersen_graph()
    matching = {edge(i, i + 5) for i in range(5)}
    f = {edge(*e) for e in p.edges()} - matching
    new_edges = {(0, 9), (1, 8), (2, 6), (3, 7), (4, 5)}
    assert not (new_edges & {edge(*e) for e in p.edges()})
    q = nx.Graph(p)
    q.add_edges_from(new_edges)
    assert nx.is_connected(q) and all(d == 4 for _, d in q.degree())
    order = sorted(edge(*e) for e in q.edges())
    w = {e: 2 if e in matching else 1 if e in f else 0 for e in order}
    assert sum(w.values()) == 20
    assert all(sum(w[edge(v, u)] for u in q[v]) == 4 for v in q)

    def rotate(c, i):
        return tuple((v + i) % 5 if v < 5 else 5 + (v - 5 + i) % 5 for v in c)

    alternating = [cycle_edges(rotate((1, 2, 7, 9, 4, 3, 8, 6), i)) for i in range(5)]
    for e in order:
        assert Fraction(sum(e in c for c in alternating), 2) == w[e]

    # An explicit signed integer combination in the FULL circuit lattice.
    signed = [(1, cycle_edges((0, 1, 2, 3, 4))),
              (1, cycle_edges((5, 7, 9, 6, 8)))]
    for i in range(5):
        a = cycle_edges(rotate((0, 1, 6, 8, 5), i))
        b = cycle_edges(rotate((0, 4, 9, 7, 5), i))
        d = cycle_edges(rotate((0, 1, 6, 8, 5, 7, 9, 4), i))
        assert a & b == {edge(i, i + 5)}
        assert a ^ b == d
        signed.extend([(1, a), (1, b), (-1, d)])
    assert all(sum(k for k, c in signed if e in c) == w[e] for e in order)

    p_cycles = all_simple_cycles(p)
    q_cycles = all_simple_cycles(q)
    p_sets = {frozenset(cycle_edges(c)) for c in p_cycles}
    assert all(frozenset(c) in p_sets for _, c in signed)
    assert all(frozenset(c) in p_sets for c in alternating)
    face = []
    for c in q_cycles:
        es = cycle_edges(c)
        slacks = []
        for v in q:
            # Valid on ALL Q cycles, including cycles using the added matching.
            slack = sum(e in es and v in e for e in set(order) - matching)
            slack -= sum(e in es and v in e for e in matching)
            assert slack in (0, 2)
            slacks.append(slack)
        if not (es & new_edges) and not any(slacks):
            face.append(es)
    assert {frozenset(c) for c in face} == {frozenset(c) for c in alternating}
    assert {len(c) for c in face} == {8}
    assert sum(w.values()) % 8 == 4  # rules out any integral circuit decomposition

    # The ten F coordinates are exactly all pair sums of five ray coefficients.
    pairs = [tuple(i for i, c in enumerate(alternating) if e in c) for e in sorted(f)]
    assert set(pairs) == set(combinations(range(5), 2))
    assert len(set(pairs)) == 10
    incidence = sp.Matrix([[int(e in c) for c in alternating] for e in order])
    assert incidence.rank() == 5
    for z in product(range(2), repeat=5):
        coeff = [Fraction(a) + Fraction(1, 2) for a in z]
        y = [sum(coeff[i] for i, c in enumerate(alternating) if e in c) for e in order]
        assert all(t.denominator == 1 for t in y)
        assert all(y[j] == w[e] + sum(z[i] for i, c in enumerate(alternating) if e in c)
                   for j, e in enumerate(order))

    # The same even simple graph has ZERO gap for the unit right-hand side.
    h1 = cycle_edges((0, 1, 2, 3, 7, 5, 8, 6, 9, 4))
    h2 = cycle_edges((0, 5, 4, 3, 8, 1, 6, 2, 7, 9))
    check_partition([as_mask(h1, order), as_mask(h2, order)], len(order))
    assert all(Fraction(len(c), 10) <= 1 for c in q_cycles)
    assert Fraction(len(order), 10) == 2
    print(f"Petersen hole: {len(p_cycles)} P cycles, {len(q_cycles)} Q cycles, "
          f"{len(face)} face rays; exact cone/lattice witnesses; c(Q)=cf(Q)=2.")
    return q


def all_bonds(g):
    """All bonds of a connected, loopless simple graph, represented by edge masks."""
    nodes = sorted(g)
    order = sorted(edge(*e) for e in g.edges())
    root, rest = nodes[0], nodes[1:]
    result = {}
    for mask in range(1 << len(rest)):
        shore = {root} | {v for i, v in enumerate(rest) if mask >> i & 1}
        other = set(nodes) - shore
        if not other:
            continue
        if nx.is_connected(g.subgraph(shore)) and nx.is_connected(g.subgraph(other)):
            cut = {e for e in order if (e[0] in shore) != (e[1] in shore)}
            cm = as_mask(cut, order)
            assert cm not in result
            result[cm] = shore
    return order, result


def cut_mask(shore, order):
    return sum(1 << i for i, (u, v) in enumerate(order) if (u in shore) != (v in shore))


def complete_bipartite_heights(a, b):
    # Root 0, in A, has height zero. This enumerates ALL unit gradients.
    out = set()
    for bh in product((-1, 1), repeat=b):
        if len(set(bh)) == 2:
            out.add((0,) * a + bh)
        else:
            t = bh[0]
            for ah in product((0, 2 * t), repeat=a - 1):
                out.add((0,) + ah + bh)
    assert len(out) == 2 ** a + 2 ** b - 2
    return sorted(out)


def check_complete_bipartite():
    graph_count = bond_count = orientation_count = 0
    k33 = None
    for a, b in product(range(2, 6), repeat=2):
        g = nx.complete_bipartite_graph(a, b)
        order, bonds = all_bonds(g)
        aa, bb = set(range(a)), set(range(a, a + b))
        m, rank = a * b, (a - 1) * (b - 1)
        longest = m - a - b + 2
        assert max(c.bit_count() for c in bonds) == longest == rank + 1
        assert len(bonds) == (2 ** a - 2) * (2 ** b - 2) // 2 + a + b
        large = [cut_mask({i} | (bb - {j}), order) for i in aa for j in bb]
        assert all(c in bonds and c.bit_count() == longest for c in large)
        assert all(sum(c >> e & 1 for c in large) == longest for e in range(m))
        cf = Fraction(m, longest)
        assert all(Fraction(c.bit_count(), longest) <= 1 for c in bonds)
        first = cut_mask({0, a}, order)
        second = ((1 << m) - 1) ^ first
        assert first in bonds and second in bonds and ((1 << m) - 1) not in bonds
        check_partition([first, second], m)
        assert cf <= 2 and (cf < 2) == (a >= 3 and b >= 3)

        fixed_values = []
        for heights in complete_bipartite_heights(a, b):
            assert all(abs(heights[u] - heights[v]) == 1 for u, v in order)
            oriented_bonds = []
            for cm, shore in bonds.items():
                signs = set()
                for e in bits(cm, m):
                    u, v = order[e]
                    if u not in shore:
                        u, v = v, u
                    signs.add(heights[v] - heights[u])
                if len(signs) == 1:
                    oriented_bonds.append(cm)
            levels = sorted(set(heights))
            if len(levels) == 2:
                stars = {cut_mask({v}, order) for v in g}
                assert set(oriented_bonds) == stars
                part = aa if a <= b else bb
                primal = [cut_mask({v}, order) for v in part]
                dual = [Fraction(1, max(a, b))] * m
                value = min(a, b)
            else:
                assert len(levels) == 3 and levels[2] - levels[0] == 2
                low = {v for v in g if heights[v] == levels[0]}
                middle = {v for v in g if heights[v] == levels[1]}
                high = {v for v in g if heights[v] == levels[2]}
                assert low and high and len(middle) >= 2
                t = {min(middle)}
                primal = [cut_mask(low | t, order), cut_mask(low | (middle - t), order)]
                dual = [Fraction(1, len(middle) * (len(low) if u in low or v in low else len(high)))
                        for u, v in order]
                value = 2
            assert all(c in oriented_bonds for c in primal)
            check_partition(primal, m)
            assert len(primal) == value == sum(dual)
            assert all(sum(dual[e] for e in bits(c, m)) <= 1 for c in oriented_bonds)
            fixed_values.append(value)
            orientation_count += 1
        assert min(fixed_values) == 2
        if (a, b) == (3, 3):
            assert cf == Fraction(9, 5)
            assert Counter(fixed_values) == {2: 12, 3: 2}
            k33 = g
        graph_count += 1
        bond_count += len(bonds)
    assert orientation_count == 448 and bond_count == 1464
    # Larger exact witnesses, without exponential all-bond enumeration.
    for a, b in [(3, 7), (4, 9), (7, 8), (10, 10), (3, 40)]:
        order = [(i, a + j) for i in range(a) for j in range(b)]
        bb = set(range(a, a + b))
        longest = a * b - a - b + 2
        family = [cut_mask({i} | (bb - {j}), order) for i in range(a) for j in bb]
        assert all(sum(c >> e & 1 for c in family) == longest for e in range(len(order)))
        c = cut_mask({0, a}, order)
        check_partition([c, ((1 << len(order)) - 1) ^ c], len(order))
    print(f"Cographic K_ab: {graph_count} exhaustive graphs, {bond_count} bonds, "
          f"{orientation_count} exact orientation optima; 5 larger unit-cover witnesses.")
    return k33


def cographic_star_partition(h):
    """Construct the blockwise-star partition, allowing parallel edges and isolates."""
    h = nx.MultiGraph(h)
    assert not list(nx.selfloop_edges(h))
    records = list(h.edges(keys=True))
    simple = nx.Graph(h)
    components = nx.number_connected_components(h)
    rank = len(records) - len(h) + components
    blocks = list(nx.biconnected_components(simple))
    cuts = []
    for block in blocks:
        bh = h.subgraph(block)
        coloring = nx.bipartite.color(bh)
        shores = [{v for v in block if coloring[v] == k} for k in (0, 1)]
        selected = min(shores, key=lambda s: (len(s), sorted(s)))
        for v in selected:
            cut = {i for i, (u, w, _) in enumerate(records) if u in block and w in block and v in (u, w)}
            assert cut
            hh = h.copy()
            hh.remove_edges_from([records[i] for i in cut])
            assert nx.number_connected_components(hh) == components + 1
            labels = {v: k for k, cc in enumerate(nx.connected_components(hh)) for v in cc}
            assert all(labels[records[i][0]] != labels[records[i][1]] for i in cut)
            cuts.append(sum(1 << i for i in cut))
    if records:
        check_partition(cuts, len(records))
    else:
        assert cuts == []
    assert len(cuts) <= rank - len(blocks)
    return len(blocks)


def has_cographic_simplicity(h):
    """No one- or two-edge cut, including when H has parallel edges."""
    h = nx.MultiGraph(h)
    if list(nx.selfloop_edges(h)):
        return False
    for comp in nx.connected_components(h):
        if len(comp) == 1:
            continue
        weighted = nx.Graph()
        weighted.add_nodes_from(comp)
        for u, v in h.subgraph(comp).edges():
            if weighted.has_edge(u, v):
                weighted[u][v]["weight"] += 1
            else:
                weighted.add_edge(u, v, weight=1)
        if nx.stoer_wagner(weighted, weight="weight")[0] < 3:
            return False
    return True


def check_cographic_rank_bound():
    total = atlas_count = 0
    for h in nx.graph_atlas_g():
        if h.number_of_edges() and nx.is_bipartite(h) and has_cographic_simplicity(h):
            cographic_star_partition(h)
            atlas_count += 1
            total += 1
    rng = random.Random(184)
    accepted = 0
    while accepted < 50:
        a, b = rng.randint(3, 6), rng.randint(3, 6)
        h = nx.Graph()
        h.add_nodes_from(range(a + b))
        probability = rng.uniform(0.55, 0.95)
        h.add_edges_from((u, a + v) for u in range(a) for v in range(b) if rng.random() < probability)
        if nx.is_connected(h) and has_cographic_simplicity(h):
            cographic_star_partition(h)
            accepted += 1
            total += 1
    for count in range(1, 9):
        h = nx.MultiGraph()
        h.add_node(0)
        next_label = 1
        for i in range(count):
            if i % 2:
                h.add_edges_from([(0, next_label)] * 3)
                next_label += 1
            else:
                k = nx.complete_bipartite_graph(3, 3)
                mapping = {0: 0, **{v: next_label + v - 1 for v in range(1, 6)}}
                h.add_edges_from((mapping[u], mapping[v]) for u, v in k.edges())
                next_label += 5
        h.add_nodes_from([next_label, next_label + 1])  # isolated vertices do not change rank
        assert nx.is_bipartite(h) and has_cographic_simplicity(h)
        assert cographic_star_partition(h) == count
        total += 1
    cographic_star_partition(nx.empty_graph(4))
    print(f"Cographic rank ledger: {total} nonempty tests ({atlas_count} atlas, "
          "50 generated, 8 block assemblies), plus edgeless case.")


def binary_columns(a):
    return [sum((int(a[i, j]) % 2) << i for i in range(a.rows)) for j in range(a.cols)]


def binary_rank(columns):
    pivots = {}
    for x in columns:
        while x:
            k = x.bit_length() - 1
            if k not in pivots:
                pivots[k] = x
                break
            x ^= pivots[k]
    return len(pivots)


def matroid_circuits(a):
    cols = binary_columns(a)
    answer = []
    for size in range(1, a.cols + 1):
        for subset in combinations(range(a.cols), size):
            value = mask = 0
            for e in subset:
                value ^= cols[e]
                mask |= 1 << e
            if value == 0 and not any(c & mask == c for c in answer):
                answer.append(mask)
    return answer


def check_tu(a):
    count = 0
    for size in range(1, min(a.rows, a.cols) + 1):
        for rr in combinations(range(a.rows), size):
            for cc in combinations(range(a.cols), size):
                assert a.extract(rr, cc).det() in (-1, 0, 1)
                count += 1
    return count


def kernel_test(rows, x):
    return all(sum(t * y for t, y in zip(row, x)) == 0 for row in rows)


def check_r10():
    b = sp.zeros(5)
    for i in range(5):
        b[i, i] = -1
        b[i, (i - 1) % 5] = b[i, (i + 1) % 5] = 1
    a = sp.eye(5).row_join(b)
    assert check_tu(a) == 3002
    assert len(set(binary_columns(a))) == 10 and 0 not in binary_columns(a)
    assert all(sum(int(a[i, j]) for j in range(10)) % 2 == 0 for i in range(5))
    circuits = matroid_circuits(a)
    assert Counter(c.bit_count() for c in circuits) == {4: 15, 6: 15}
    fours = []
    for i in range(5):
        types = [
            {(i - 1) % 5, i, (i + 1) % 5, 5 + i},
            {i, (i + 2) % 5, 5 + (i + 3) % 5, 5 + (i + 4) % 5},
            {i, 5 + i, 5 + (i + 2) % 5, 5 + (i + 3) % 5},
        ]
        fours.extend(sum(1 << e for e in c) for c in types)
    assert set(fours) == {c for c in circuits if c.bit_count() == 4}
    sixes = [1023 ^ c for c in fours]
    assert set(sixes) == {c for c in circuits if c.bit_count() == 6}
    assert all(sum(c >> e & 1 for c in sixes) == 9 for e in range(10))
    assert all(Fraction(c.bit_count(), 6) <= 1 for c in circuits)
    check_partition([fours[0], 1023 ^ fours[0]], 10)
    assert len(exact_min_partition(circuits, 10)) == 2
    rows = [[int(v) for v in row] for row in a.tolist()]
    signatures = [s for s in product((-1, 1), repeat=10) if kernel_test(rows, s)]
    assert len(signatures) == 12
    for s in signatures:
        positive = [c for c in circuits if kernel_test(rows, [s[e] if c >> e & 1 else 0 for e in range(10)])]
        assert Counter(c.bit_count() for c in positive) == {4: 5, 6: 5}
        long = [c for c in positive if c.bit_count() == 6]
        assert all(sum(c >> e & 1 for c in long) == 3 for e in range(10))
        partition = exact_min_partition(positive, 10)
        assert len(partition) == 2
        check_partition(partition, 10)
    print("R10: all 3002 square minors TU; 15 four- and 15 six-circuits; "
          "12 unit orientations; cf=mu_f=5/3 and c=2, with exact witnesses.")
    return a


def incidence(g):
    vertices = sorted(g)
    order = sorted(edge(*e) for e in g.edges())
    rows = vertices[:-1]
    a = sp.zeros(len(rows), len(order))
    for j, (u, v) in enumerate(order):
        if u in rows:
            a[rows.index(u), j] = -1
        if v in rows:
            a[rows.index(v), j] = 1
    return a, order


def cographic_representation(g):
    b, order = incidence(g)
    tree_edges = {edge(*e) for e in nx.minimum_spanning_tree(g).edges()}
    tree = [i for i, e in enumerate(order) if e in tree_edges]
    cotree = [i for i, e in enumerate(order) if e not in tree_edges]
    network = b[:, tree].inv() * b[:, cotree]
    a = sp.zeros(len(cotree), len(order))
    for i, j in enumerate(tree):
        for k in range(len(cotree)):
            a[k, j] = -network[i, k]
    for i, j in enumerate(cotree):
        a[i, j] = 1
    assert a * b.T == sp.zeros(a.rows, b.rows)
    return a


def check_orientation_cube(r10, k33):
    g5, _ = incidence(nx.complete_graph(5))
    g4, _ = incidence(nx.complete_graph(4))
    dual33 = cographic_representation(k33)
    matrices = [("graphic K5", g5, True, 24), ("cographic K33", dual33, True, 14),
                ("R10", r10, True, 12), ("non-Eulerian graphic K4", g4, False, 14)]
    minor_count = 0
    for name, a, eulerian, expected in matrices:
        if name != "R10":
            minor_count += check_tu(a)
        rows = [[int(v) for v in row] for row in a.tolist()]
        cols = binary_columns(a)
        vertices = []
        for q in product((-1, 0, 1), repeat=a.cols):
            if not kernel_test(rows, q):
                continue
            zeros = [cols[j] for j, x in enumerate(q) if x == 0]
            # TU identifies real and binary column independence.
            if binary_rank(zeros) == len(zeros):
                vertices.append(q)
        assert len(vertices) == expected
        if eulerian:
            assert all(0 not in q for q in vertices)
            circuits = matroid_circuits(a)
            for q in vertices:
                positive = [c for c in circuits if kernel_test(rows, [q[e] if c >> e & 1 else 0 for e in range(a.cols)])]
                partition = exact_min_partition(positive, a.cols)
                assert partition is not None and len(partition) <= a.cols - a.rows
                check_partition(partition, a.cols)
        else:
            assert all(0 in q for q in vertices)
        print(f"Orientation cube: {name}: {len(vertices)} exact vertices; Eulerian={eulerian}.")
    assert minor_count == 1797
    print("Additional representation checks: all 1797 square minors TU.")


def main():
    check_spec()
    check_petersen_hole()
    k33 = check_complete_bipartite()
    check_cographic_rank_bound()
    r10 = check_r10()
    check_orientation_cube(r10, k33)
    check_spec()
    print("ALL EXACT CHECKS PASSED; protected Spec hash unchanged.")


if __name__ == "__main__":
    main()
