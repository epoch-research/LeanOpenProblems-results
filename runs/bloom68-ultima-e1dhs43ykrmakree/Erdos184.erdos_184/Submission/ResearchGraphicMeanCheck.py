#!/usr/bin/env python3
"""Exact audits for ResearchGraphicMean.md; standard library only.

The general recursions/localization inequality are proved in the note.
This checks their finite certificates, not a universal Erdős--Gallai theorem.
No LP solver, numerical tolerance, old checker import, or file writes are used.
All means are over complete cycle spaces (or the explicitly named affine fiber).
"""
from __future__ import annotations

from collections import Counter, defaultdict
from fractions import Fraction as R
from hashlib import sha256
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC_SHA256 = "429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde"


def snapshot():
    paths = [p for name in ("Submission", "newSubmission")
             for p in (ROOT / name).rglob("*") if p.is_file()]
    paths.append(ROOT / "Check.py")
    return {str(p.relative_to(ROOT)): sha256(p.read_bytes()).hexdigest()
            for p in paths}


def bits(x):
    while x:
        b = x & -x
        yield b.bit_length() - 1
        x ^= b


def rank(rows):
    pivots = {}
    for x in rows:
        while x:
            k = x.bit_length() - 1
            if k not in pivots:
                pivots[k] = x
                break
            x ^= pivots[k]
    return len(pivots)


def span(basis):
    out = [0]
    for b in basis:
        out += [w ^ b for w in out]
    assert len(set(out)) == 1 << len(basis)
    return out


class Graph:
    """Loopless multigraph used as a compact certificate; 2-cycles are allowed.

    All multigraph examples below are also explicitly expanded to simple graphs.
    """
    def __init__(self, n, edges):
        self.n = n
        self.edges = [tuple(sorted(e)) for e in edges]
        assert all(0 <= u < v < n for u, v in self.edges)
        self.m = len(self.edges)
        self.E = (1 << self.m) - 1
        self.adj = [[] for _ in range(n)]
        self.stars = [0] * n
        for i, (u, v) in enumerate(self.edges):
            self.adj[u].append((v, i))
            self.adj[v].append((u, i))
            self.stars[u] |= 1 << i
            self.stars[v] |= 1 << i
        self.components = self.component_count(self.E)
        pivots, basis = {}, []
        for i, (u, v) in enumerate(self.edges):
            x, w = (1 << u) ^ (1 << v), 1 << i
            while x:
                k = x.bit_length() - 1
                if k not in pivots:
                    pivots[k] = x, w
                    break
                old, oldw = pivots[k]
                x ^= old
                w ^= oldw
            if not x:
                basis.append(w)
        self.basis = basis
        self.dim = len(basis)
        assert len(pivots) == n - self.components
        assert self.dim == self.m - n + self.components
        assert rank(basis) == self.dim
        assert all(self.even(b) for b in basis)

    def even(self, w):
        return all((w & s).bit_count() % 2 == 0 for s in self.stars)

    def degrees(self, w):
        return [(w & s).bit_count() for s in self.stars]

    def words(self):
        assert self.dim <= 20, "Only explicitly small full spaces are enumerated"
        return span(self.basis)

    def component_count(self, w, vertices=None):
        unseen = set(range(self.n)) if vertices is None else set(vertices)
        count = 0
        while unseen:
            count += 1
            stack = [unseen.pop()]
            while stack:
                v = stack.pop()
                for u, e in self.adj[v]:
                    if (w >> e) & 1 and u in unseen:
                        unseen.remove(u)
                        stack.append(u)
        return count

    def is_cycle(self, w):
        deg = self.degrees(w)
        if not w or any(d not in (0, 2) for d in deg):
            return False
        active = [v for v, d in enumerate(deg) if d]
        return self.component_count(w, active) == 1

    def cycles(self):
        out = set()
        for s in range(self.n):
            def dfs(u, visited, mask):
                for v, i in self.adj[u]:
                    if (mask >> i) & 1:
                        continue
                    if v == s:
                        out.add(mask | (1 << i))
                    elif v > s and not (visited >> v) & 1:
                        dfs(v, visited | (1 << v), mask | (1 << i))
            dfs(s, 1 << s, 0)
        assert all(self.is_cycle(c) for c in out)
        return sorted(out)

    def cycle_mask(self, vertices):
        assert len(vertices) >= 3 and len(set(vertices)) == len(vertices)
        index = {e: i for i, e in enumerate(self.edges)}
        assert len(index) == self.m, "Vertex-list certificates here use simple graphs"
        es = [tuple(sorted((vertices[i - 1], v)))
              for i, v in enumerate(vertices)]
        assert all(e in index for e in es)
        w = sum(1 << index[e] for e in es)
        assert w.bit_count() == len(vertices) and self.is_cycle(w)
        return w


def project(w, old_indices):
    return sum(1 << j for j, i in enumerate(old_indices) if (w >> i) & 1)


def projection_audit(g, target, old_indices, enumerate_fibers=False):
    images = [project(w, old_indices) for w in g.basis]
    assert all(target.even(w) for w in images)
    assert rank(images) == target.dim
    if enumerate_fibers:
        counts = Counter(project(w, old_indices) for w in g.words())
        assert set(counts) == set(target.words())
        assert set(counts.values()) == {1 << (g.dim - target.dim)}


def expand_simple(g):
    edges = []
    for i, (u, v) in enumerate(g.edges):
        edges += [(u, g.n + i), (g.n + i, v)]
    out = Graph(g.n + g.m, edges)
    assert len(set(out.edges)) == out.m
    assert out.dim == g.dim and out.components == g.components
    return out


def lift(w):
    return sum(3 << (2 * i) for i in bits(w))


def unlift(w, m):
    assert all(((w >> (2 * i)) & 3) in (0, 3) for i in range(m))
    return sum(1 << i for i in range(m) if (w >> (2 * i)) & 1)


def cycle_bundles(multiplicities):
    assert len(multiplicities) >= 3 and min(multiplicities) >= 1
    edges, groups = [], []
    for i, m in enumerate(multiplicities):
        group = list(range(len(edges), len(edges) + m))
        groups.append(group)
        edges += [(i, (i + 1) % len(multiplicities))] * m
    return Graph(len(multiplicities), edges), groups


def bundle_value(w, groups):
    q = [sum((w >> i) & 1 for i in group) for group in groups]
    assert len({x % 2 for x in q}) == 1
    return R(sum(q) - (len(groups) - 2) * min(q), 2)


def bundle_certificate(w, groups):
    present = [[i for i in group if (w >> i) & 1] for group in groups]
    r = min(map(len, present))
    j = min(range(len(groups)), key=lambda k: len(present[k]))
    parts = [sum(1 << p[k] for p in present) for k in range(r)]
    for p in present:
        assert (len(p) - r) % 2 == 0
        parts += [(1 << p[k]) | (1 << p[k + 1])
                  for k in range(r, len(p), 2)]
    m = sum(map(len, groups))
    y = [R(0)] * m
    for k, p in enumerate(present):
        for i in p:
            y[i] = R(3 - len(groups), 2) if k == j else R(1, 2)
    val = bundle_value(w, groups)
    assert len(parts) == val
    return val, parts, y


def check_certificate(g, cycles, w, val, parts, y):
    used = 0
    for c in parts:
        assert c in cycles and not (c & used) and not (c & ~w)
        used |= c
    assert used == w and len(parts) == val
    assert sum(y[i] for i in bits(w)) == val
    for c in cycles:
        if c & ~w == 0:
            assert sum(y[i] for i in bits(c)) <= 1


def audit_bundle(g, groups):
    words = g.words()
    cycles = set(g.cycles())
    assert cycles == {w for w in words if g.is_cycle(w)}
    simple = expand_simple(g)
    assert {unlift(w, g.m) for w in simple.words()} == set(words)
    assert all(simple.is_cycle(lift(c)) for c in cycles)
    total = R(0)
    for w in words:
        val, parts, y = bundle_certificate(w, groups)
        check_certificate(g, cycles, w, val, parts, y)
        total += val
    return total / len(words)


def chain_profile(q):
    """Actual fractional profile for a series chain of parallel-edge traces.

    Returns (lower traffic, upper traffic, intercept, slope). In an odd fiber
    the fractional lower endpoint can be ZERO; parity is imposed only on
    integral partitions. In particular we do not silently impose integer parity
    on the fractional program.
    """
    lo, hi = max(int(x == 1) for x in q), min(q)
    assert lo <= hi
    return R(lo), R(hi), R(sum(q), 2), R(-len(q), 2)


def profile_at(profile, p):
    lo, hi, intercept, slope = profile
    assert lo <= p <= hi
    return intercept + slope * p


def parallel_at_zero(x, y):
    lo, hi = max(x[0], y[0]), min(x[1], y[1])
    assert lo <= hi
    # At output traffic zero the two child traffic masses equal p, and p
    # cross-cycles are formed. This minimizes the true affine objectives.
    return min(profile_at(x, p) + profile_at(y, p) + p for p in (lo, hi))


def conditional_profile_example():
    examples = [(((2, 6), (4, 4)), (R(2), R(1)),
                 [R(545, 256), R(527, 256)]),
                (((2, 2, 6, 2), (2, 4, 4, 2)), (R(3), R(1)),
                 [R(2723, 1024), R(2669, 1024)])]
    for inputs, expected_pair, expected_answers in examples:
        answers = []
        for mult in inputs:
            profiles = {0: [], 1: []}
            for choices in product(*(range(1 << m) for m in mult)):
                q = [c.bit_count() for c in choices]
                if len({x % 2 for x in q}) != 1:
                    continue
                b = q[0] % 2
                profiles[b].append(chain_profile(q))
            count = 1 << (sum(mult) - len(mult))
            assert len(profiles[0]) == len(profiles[1]) == count
            pair = tuple(sum(profile_at(p, b) for p in profiles[b]) / count
                         for b in (0, 1))
            assert pair == expected_pair
            cost = R(0)
            cases = 0
            for b in (0, 1):
                for x in profiles[b]:
                    for return_mask in range(4):
                        if return_mask.bit_count() % 2 != b:
                            continue
                        y = chain_profile([return_mask.bit_count()])
                        cost += parallel_at_zero(x, y)
                        cases += 1
            assert cases == 4 * count
            mean = cost / cases
            g, groups = cycle_bundles(mult + (2,))
            certified = audit_bundle(g, groups)
            assert certified == mean and bundle_value(g.E, groups) == 4
            answers.append(mean)
        assert answers == expected_answers
    print("Scalar conditional means fail to close under parallel composition:")
    print("  input pair (M0,M1)=(2,1): output a=545/256 versus 527/256.")
    print("  even with the same terminal degrees, size and nullity, pair (3,1)")
    print("  gives output a=2723/1024 versus 2669/1024.")


def unbounded_conditional_imbalance():
    for length in range(2, 6):
        g, groups = cycle_bundles((3,) * length + (1,))
        mark = groups[-1][0]
        sums, counts = [R(0), R(0)], [0, 0]
        cycles = set(g.cycles())
        for w in g.words():
            b = (w >> mark) & 1
            val, parts, y = bundle_certificate(w, groups)
            check_certificate(g, cycles, w, val, parts, y)
            sums[b] += val
            counts[b] += 1
        assert counts == [1 << (2 * length)] * 2
        assert sums[0] / counts[0] == R(3 * length, 4)
        assert sums[1] / counts[1] == 1 + R(length, 4)
        assert sum(sums) / sum(counts) == R(length + 1, 2)
        assert bundle_value(g.E, groups) == length + 1
    print("Odd-chain family: A0=3l/4, A1=1+l/4, a=(l+1)/2, c=l+1.")


def split_vertex(g, vertex, moved_edges):
    moved_edges = set(moved_edges)
    out = []
    for i, (u, v) in enumerate(g.edges):
        if i in moved_edges:
            assert vertex in (u, v)
            u = g.n if u == vertex else u
            v = g.n if v == vertex else v
        out.append((u, v))
    h = Graph(g.n + 1, out)
    assert h.even(h.E)
    return h


def doubled_cycle_mean(n):
    return R(n + 2, 4) - R(n - 2, 1 << (n + 1))


def vertex_split_audit():
    for n in range(4, 9):
        g, groups = cycle_bundles((2,) * n)
        a = sum(bundle_value(w, groups) for w in g.words()) / (1 << g.dim)
        assert a == doubled_cycle_mean(n)
        # Move both edges of one parallel pair: a doubled path.
        moved = groups[0]
        split = split_vertex(g, 0, moved)
        words = split.words()
        assert split.components == 1 and split.dim == g.dim - 1
        assert set(words) == {w for w in g.words()
                              if sum((w >> i) & 1 for i in moved) % 2 == 0}
        assert all(c.bit_count() == 2 for c in split.cycles())
        split_mean = sum(R(w.bit_count(), 2) for w in words) / len(words)
        old_conditional = sum(bundle_value(w, groups) for w in words) / len(words)
        assert split_mean == R(n, 2)
        assert old_conditional == R(n, 2) - R(n - 2, 1 << n)
        assert split_mean - a == R(n - 2, 4) + R(n - 2, 1 << (n + 1))
        # Move one edge from each incident pair: after series suppression this
        # is the doubled cycle with one fewer junction.
        mixed = split_vertex(g, 0, [groups[0][0], groups[-1][0]])
        h, hgroups = cycle_bundles((2,) * (n - 1))
        images = []
        for w in mixed.words():
            assert ((w >> groups[0][0]) & 1) == ((w >> groups[-1][0]) & 1)
            assert ((w >> groups[0][1]) & 1) == ((w >> groups[-1][1]) & 1)
            old = [i for group in groups[1:-1] for i in group] + groups[0]
            images.append(project(w, old))
        assert len(set(images)) == len(images) and set(images) == set(h.words())
        assert {project(c, old) for c in mixed.cycles()} == set(h.cycles())
        mixed_mean = sum(bundle_value(w, hgroups) for w in images) / len(images)
        assert mixed_mean == doubled_cycle_mean(n - 1)
        assert a - mixed_mean == R(1, 4) + R(n - 4, 1 << (n + 1))
        assert bundle_value(g.E, groups) == bundle_value(h.E, hgroups) == 2
        # The split multigraphs really have simple subdivisions.
        assert len(set(expand_simple(split).edges)) == 2 * split.m
        assert len(set(expand_simple(mixed).edges)) == 2 * mixed.m
    print("Even vertex-split hyperplanes: doubled-path and shorter-doubled-cycle formulas checked.")


def cap(g, vertices):
    vertices = sorted(vertices)
    idx = {v: j for j, v in enumerate(vertices)}
    anchor = len(vertices)
    edges, old = [], []
    for i, (u, v) in enumerate(g.edges):
        if u not in idx and v not in idx:
            continue
        edges.append((idx.get(u, anchor), idx.get(v, anchor)))
        old.append(i)
    return Graph(anchor + 1, edges), old, anchor


def quotient(g, parts):
    owner = {v: i for i, part in enumerate(parts) for v in part}
    assert len(owner) == g.n
    edges, old = [], []
    for i, (u, v) in enumerate(g.edges):
        if owner[u] != owner[v]:
            edges.append((owner[u], owner[v]))
            old.append(i)
    return Graph(len(parts), edges), old


def groups_from_doubled_cycle(g):
    groups = defaultdict(list)
    for i, e in enumerate(g.edges):
        groups[e].append(i)
    assert len(groups) == g.n and all(len(x) == 2 for x in groups.values())
    simple_degree = Counter(v for e in groups for v in e)
    assert set(simple_degree.values()) == {2} and g.components == 1
    return list(groups.values())


def localization_audit():
    for sizes in ((3, 3), (3, 2, 3)):
        n = sum(sizes)
        g, groups = cycle_bundles((2,) * n)
        parts, pos = [], 0
        for size in sizes:
            parts.append(set(range(pos, pos + size)))
            pos += size
        caps = []
        for part in parts:
            assert g.component_count(g.E, part) == 1
            assert g.component_count(g.E, set(range(n)) - part) == 1
            h, old, v = cap(g, part)
            projection_audit(g, h, old, enumerate_fibers=True)
            caps.append((h, old, v, groups_from_doubled_cycle(h)))
        q, oldq = quotient(g, parts)
        projection_audit(g, q, oldq, enumerate_fibers=True)
        total, bound = R(0), R(0)
        for w in g.words():
            value = bundle_value(w, groups)
            rhs = R(bool(project(w, oldq)))
            for h, old, v, hgroups in caps:
                image = project(w, old)
                residual = bundle_value(image, hgroups) - R((image & h.stars[v]).bit_count(), 2)
                assert residual >= 0
                rhs += residual
            assert value >= rhs
            total += value
            bound += rhs
        a, lower = total / (1 << g.dim), bound / (1 << g.dim)
        expression = 1 - R(1, 1 << q.dim)
        for h, _, v, hgroups in caps:
            expression += (sum(bundle_value(w, hgroups) for w in h.words()) / (1 << h.dim)
                           - R(h.stars[v].bit_count(), 4))
        assert expression == lower
        print(f"Localization audit on doubled cycle with block sizes {sizes}: a={a}, lower={lower}.")


def graphic_anchor_gluing():
    factors = []
    for n in (3, 4):
        core, groups = cycle_bundles((2,) * n)
        factors.append((core, groups, expand_simple(core)))
    g1, g2 = [x[2] for x in factors]
    u1, v1 = g1.edges[0]
    u2, v2 = g2.edges[0]
    # Identify v1 with u2 and add one retained anchor u1--v2.
    mapping1 = list(range(g1.n))
    mapping2 = []
    next_vertex = g1.n
    for v in range(g2.n):
        if v == u2:
            mapping2.append(v1)
        else:
            mapping2.append(next_vertex)
            next_vertex += 1
    edges = [(u1, mapping2[v2])]
    traces = []
    for graph, mapping in ((g1, mapping1), (g2, mapping2)):
        trace = {0: 0}
        for i, (u, v) in enumerate(graph.edges):
            if i == 0:
                continue
            trace[i] = len(edges)
            edges.append((mapping[u], mapping[v]))
        traces.append(trace)
    glued = Graph(next_vertex, edges)
    assert len(set(glued.edges)) == glued.m and glued.even(glued.E)
    assert glued.dim == g1.dim + g2.dim - 1
    cycles = set(glued.cycles())
    sums, marginals = R(0), [Counter(), Counter()]
    for w in glued.words():
        gbit = w & 1
        costs, parts_by_factor, duals = [], [], []
        for k, (core, groups, graph) in enumerate(factors):
            trace = traces[k]
            image = sum(1 << i for i, e in trace.items() if (w >> e) & 1)
            assert graph.even(image)
            marginals[k][image] += 1
            cw = unlift(image, core.m)
            value, parts, dual = bundle_certificate(cw, groups)
            costs.append(value)
            parts_by_factor.append([lift(c) for c in parts])
            duals.append([z for y in dual for z in (y, R(0))])
        parts, marked = [], []
        for k, local_parts in enumerate(parts_by_factor):
            for c in local_parts:
                image = sum(1 << traces[k][i] for i in bits(c))
                if c & 1:
                    marked.append(image)
                else:
                    parts.append(image)
        if gbit:
            assert len(marked) == 2
            parts.append(marked[0] | marked[1])
        else:
            assert not marked
        dual = [R(0)] * glued.m
        for k, ys in enumerate(duals):
            for i, e in traces[k].items():
                if i:
                    dual[e] = ys[i]
        dual[0] = sum(ys[0] for ys in duals) - 1
        value = sum(costs) - gbit
        check_certificate(glued, cycles, w, value, parts, dual)
        sums += value
    for k, (_, _, graph) in enumerate(factors):
        assert set(marginals[k]) == set(graph.words())
        assert set(marginals[k].values()) == {1 << (glued.dim - graph.dim)}
    assert sums / (1 << glued.dim) == R(17, 8)
    assert sum(bundle_value(core.E, groups) for core, groups, _ in factors) - 1 == 3
    print("Retained-anchor gluing is actually simple graphic: c=3, a=17/8; all 256 words certified.")


def petersen_line_graph():
    pe = set()
    for i in range(5):
        pe.add(tuple(sorted((i, (i + 1) % 5))))
        pe.add((i, i + 5))
        pe.add(tuple(sorted((5 + i, 5 + (i + 2) % 5))))
    pe = sorted(pe)
    assert pe == [(0, 1), (0, 4), (0, 5), (1, 2), (1, 6), (2, 3), (2, 7),
                  (3, 4), (3, 8), (4, 9), (5, 7), (5, 8), (6, 8), (6, 9), (7, 9)]
    edges = [(i, j) for i in range(15) for j in range(i + 1, 15) if set(pe[i]) & set(pe[j])]
    return Graph(15, edges)


HAMILTON = {
    (0, 0): (0, 1, 2, 10, 14, 9, 13, 4, 12, 11, 8, 7, 5, 6, 3),
    (0, 1): (0, 1, 9, 7, 5, 3, 6, 14, 10, 2, 11, 8, 12, 13, 4),
    (1, 1): (0, 2, 1, 7, 9, 13, 14, 6, 10, 11, 12, 8, 5, 3, 4),
    (1, 0): (0, 2, 11, 10, 6, 5, 8, 7, 1, 9, 14, 13, 12, 4, 3),
}
B_CYCLE = (0, 2, 11, 10, 6, 14, 13, 12, 8, 5, 3, 4)
T_CYCLE = (1, 7, 9)


def petersen_degree_certificate():
    g = petersen_line_graph()
    assert g.dim == 16 and g.degrees(g.E) == [4] * 15
    S = (0, 1, 2, 3, 5, 12, 14)
    internal = {e for e in g.edges if set(e) <= set(S)}
    assert internal == {(0, 1), (0, 2), (1, 2), (0, 3), (3, 5)}
    outside = set(range(15)) - set(S)
    outside_path = (4, 13, 9, 7, 8, 11, 10, 6)
    assert set(outside_path) == outside
    outside_edges = {tuple(sorted((a, b))) for a, b in zip(outside_path, outside_path[1:])}
    assert {e for e in g.edges if set(e) <= outside} == outside_edges
    assert all(any(u in outside for u, _ in g.adj[v]) for v in S)
    no_four = R(0)
    for mask in range(1 << len(S)):
        A = {S[i] for i in bits(mask)}
        star = 0
        for v in A:
            star |= g.stars[v]
        indices = list(bits(star))
        eA = sum(set(e) <= A for e in g.edges)
        r = 3 * len(A) - eA
        assert rank(project(b, indices) for b in g.basis) == r
        assert g.component_count(g.E, set(range(15)) - A) == 1
        no_four += (-1) ** len(A) * R(1, 1 << r)
    assert no_four == R(285, 512) * R(7, 8) ** 2 == R(13965, 32768)
    seven_bound = 2 - no_four - R(1, 1 << 16)
    assert seven_bound == R(103141, 65536) > R(25, 16)
    # Independent full-code audit of the seven-star certificate, and an
    # optional sharpening by using every vertex. Neither is the exact mean cf.
    seven_counts, all_counts = Counter(), Counter()
    for w in g.words():
        deg = g.degrees(w)
        seven_counts[max(deg[v] for v in S)] += 1
        all_counts[max(deg)] += 1
    assert seven_counts == {0: 1, 2: 27929, 4: 37606}
    assert all_counts == {0: 1, 2: 13347, 4: 52188}
    all_bound = sum(R(d, 2) * n for d, n in all_counts.items()) / (1 << 16)
    assert all_bound == R(117723, 65536)
    assert sum(R(d, 2) * n for d, n in seven_counts.items()) / (1 << 16) == seven_bound
    # Each degree lower bound has a genuine all-simple-cycle dual: price 1/2
    # on the star of a maximizing vertex, zero elsewhere. Check all full cycles
    # independently by DFS and by the cycle-space characterization.
    cycles = set(g.cycles())
    assert len(cycles) == 7514
    assert cycles == {w for w in g.words() if g.is_cycle(w)}
    assert all(max(g.degrees(c)) == 2 for c in cycles)
    hs = [g.cycle_mask(c) for c in HAMILTON.values()]
    assert all(sum((c >> i) & 1 for c in hs) == 2 for i in range(g.m))
    part = [hs[0], g.cycle_mask(B_CYCLE), g.cycle_mask(T_CYCLE)]
    assert sum(part) == g.E and all(part[i] & part[j] == 0 for i in range(3) for j in range(i))
    print("Petersen seven-star paper certificate: E max_S degree/2=103141/65536 > 25/16.")
    print("  Independent full-code degree bound: a(L(P)) >= 117723/65536 (not an exact a value).")
    return g, seven_bound, all_bound


def petersen_ring_audit(base, seven_bound, all_bound):
    for t in (2, 3, 4, 5, 8, 16):
        def v(i, label):
            return 14 * i + label - 1
        edges = [(v(i, a), v(i, b)) for i in range(t)
                 for a, b in base.edges if 0 not in (a, b)]
        for i in range(t):
            edges += [(v(i, 3), v((i + 1) % t, 1)),
                      (v(i, 4), v((i + 1) % t, 2))]
        g = Graph(14 * t, edges)
        assert g.m == 28 * t and g.dim == 14 * t + 1
        assert len(set(g.edges)) == g.m and g.degrees(g.E) == [4] * g.n
        parts = [set(range(14 * i, 14 * (i + 1))) for i in range(t)]
        for i, part in enumerate(parts):
            assert g.component_count(g.E, part) == 1
            assert g.component_count(g.E, set(range(g.n)) - part) == 1
            h, old, anchor = cap(g, part)
            assert anchor == 14 and h.dim == 16
            relabel = lambda u: 0 if u == anchor else u + 1
            assert sorted(tuple(sorted((relabel(a), relabel(b)))) for a, b in h.edges) == base.edges
            projection_audit(g, h, old)
        q, oldq = quotient(g, parts)
        assert q.dim == t + 1
        projection_audit(g, q, oldq)
        # Explicit t+2 simple-cycle partition; exact optimality is unnecessary
        # for the new mean inequality.
        big1 = [v(i, a) for i in range(t) for a in HAMILTON[(0, 0)][1:]]
        big2 = [v(i, a) for i in range(t) for a in B_CYCLE[1:]]
        partition = [g.cycle_mask(big1), g.cycle_mask(big2)]
        partition += [g.cycle_mask([v(i, a) for a in T_CYCLE]) for i in range(t)]
        used = 0
        for c in partition:
            assert not c & used
            used |= c
        assert used == g.E and len(partition) == t + 2
        # Independent full cf=2 certificate on these rings (four Hamilton
        # cycles of coefficient 1/2, and the length dual 1/(14t)).
        forms = ([1 if i % 2 == 0 else 2 for i in range(t)] if t % 2 == 0
                 else [1 if i % 2 == 0 else 2 for i in range(t - 1)] + [3])
        assert all(forms[i - 1] != forms[i] for i in range(t))
        cover = []
        for z in range(4):
            s = [(f & z).bit_count() % 2 for f in forms]
            path = [v(i, a) for i in range(t)
                    for a in HAMILTON[(s[i - 1], s[i])][1:]]
            assert len(path) == g.n and len(set(path)) == g.n
            cover.append(g.cycle_mask(path))
        assert all(sum((c >> i) & 1 for c in cover) == 2 for i in range(g.m))
        assert R(g.m, g.n) == 2
        lower = (seven_bound - 1) * t + 1 - R(1, 1 << (t + 1))
        simple_lower = R(9 * t, 16) + 1 - R(1, 1 << (t + 1))
        assert lower > simple_lower >= R(t + 2, 2)
        sharpened = (all_bound - 1) * t + 1 - R(1, 1 << (t + 1))
        assert R(13, 8) * sharpened >= t + 2
    # Algebraic all-t checks: at t=2 the relevant inequalities hold, and their
    # linear terms increase while 2^(-t-1) decreases. These are not extrapolations.
    assert R(2, 16) == R(1, 1 << 3)
    rho = all_bound - 1
    assert R(13, 8) * rho - 1 > 0
    assert R(13, 8) * (2 * rho + 1 - R(1, 8)) - 4 == R(2591, 262144) > 0
    print("Petersen rings: cap surjectivity, quotient rank, simple partitions, and half-covers checked.")
    print("  For ALL t>=2, the analytic bound proves c(R_t)<=2a(R_t).")
    print("  The stronger exact finite degree certificate gives c(R_t)<=(13/8)a(R_t).")
    print("  No full large-ring cycle space was enumerated, and no exact a(R_t) was claimed.")


def main():
    before = snapshot()
    assert before["Submission/Spec.lean"] == SPEC_SHA256
    conditional_profile_example()
    unbounded_conditional_imbalance()
    vertex_split_audit()
    localization_audit()
    graphic_anchor_gluing()
    base, seven, all_vertices = petersen_degree_certificate()
    petersen_ring_audit(base, seven, all_vertices)
    assert before == snapshot(), "An existing file changed during the checker"
    print(f"PASS: exact rational checks; {len(before)} file hashes unchanged during execution.")
    print("UNRESOLVED: a universal finite K for all even simple graphic graphs, including K=2.")


if __name__ == "__main__":
    main()
