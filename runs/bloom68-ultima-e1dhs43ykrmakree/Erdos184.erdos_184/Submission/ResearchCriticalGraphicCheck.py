#!/usr/bin/env python3
"""Exact certificates for ResearchCriticalGraphic.md (standard library only).

This is NOT an Erdős--Gallai/Hajós proof or a search-based general theorem.
It enumerates the COMPLETE binary cycle spaces of the actual simple graphs
being certified. Simple cycles are independently identified in two ways.
Minimum and maximum partition counts use an exhaustive, first-edge DP.
All fractional certificates are checked with fractions.Fraction.

Run: python3 Submission/ResearchCriticalGraphicCheck.py
Optional: --dump-restrictions /some/new/directory
The optional JSONL files contain every even restriction and its DP witnesses.
Optional: --graph-json graph.json, with keys n and edges. This also extracts
an inclusion-minimal maximum-Q restriction and checks exact certificates.
The exhaustive diagnostic is capped at cycle-space dimension 20.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as R
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

SPEC_SHA256 = "429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde"


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def edge(u, v):
    assert u != v
    return min(u, v), max(u, v)


def binary_rank(vectors):
    pivots = {}
    for v in vectors:
        while v:
            k = v.bit_length() - 1
            if k not in pivots:
                pivots[k] = v
                break
            v ^= pivots[k]
    return len(pivots)


class GraphAudit:
    """No graph library, LP solver, old checker, or assumed circuit list."""

    def __init__(self, n, edges, name):
        self.n, self.name = n, name
        self.edges = [edge(*uv) for uv in edges]
        assert len(set(self.edges)) == len(self.edges), "Graph must be simple"
        assert all(0 <= u < v < n for u, v in self.edges)
        self.m = len(self.edges)
        self.E = (1 << self.m) - 1
        self.index = {uv: i for i, uv in enumerate(self.edges)}
        self.adj = [[] for _ in range(n)]
        for i, (u, v) in enumerate(self.edges):
            self.adj[u].append((v, i))
            self.adj[v].append((u, i))
        assert all(len(a) % 2 == 0 for a in self.adj)

        # Connected-component count includes isolated vertices.
        unseen = set(range(n))
        self.components = 0
        while unseen:
            self.components += 1
            stack = [unseen.pop()]
            while stack:
                u = stack.pop()
                for v, _ in self.adj[u]:
                    if v in unseen:
                        unseen.remove(v)
                        stack.append(v)

        # Gaussian elimination of incidence columns, tracking all relations.
        pivots, basis = {}, []
        for i, (u, v) in enumerate(self.edges):
            col, word = (1 << u) ^ (1 << v), 1 << i
            while col:
                k = col.bit_length() - 1
                if k not in pivots:
                    pivots[k] = col, word
                    break
                old_col, old_word = pivots[k]
                col ^= old_col
                word ^= old_word
            if not col:
                basis.append(word)
        self.basis = basis
        self.dimension = len(basis)
        assert len(pivots) == n - self.components
        assert self.dimension == self.m - n + self.components
        assert binary_rank(basis) == self.dimension
        if self.dimension > 20:
            raise ValueError("This small-graph diagnostic caps the cycle-space dimension at 20")
        words = [0]
        for b in basis:
            words += [w ^ b for w in words]
        assert len(set(words)) == 1 << self.dimension
        self.words = sorted(words, key=lambda w: (w.bit_count(), w))
        self.word_set = set(words)
        assert self.E in self.word_set

        # First cycle enumeration: vertex-simple DFS, with both symmetries cut.
        cycles = set()
        for start in range(n):
            def dfs(u, path, visited, mask):
                for v, i in self.adj[u]:
                    if v == start:
                        if len(path) >= 3 and path[1] < path[-1]:
                            cycles.add(mask | (1 << i))
                    elif v > start and not (visited >> v) & 1:
                        dfs(v, path + [v], visited | (1 << v), mask | (1 << i))
            dfs(start, [start], 1 << start, 0)
        self.cycles = sorted(cycles, key=lambda c: (-c.bit_count(), c))
        self.cycle_set = cycles
        self.by_edge = [[] for _ in self.edges]
        for c in self.cycles:
            for i in bits(c):
                self.by_edge[i].append(c)

        # Second, independent characterization: connected, nonempty, 2-regular.
        # All words are even. Incidence rank proves there are no missing words.
        recognized = set()
        for w in self.words:
            deg = [0] * n
            for i in bits(w):
                u, v = self.edges[i]
                deg[u] += 1
                deg[v] += 1
            assert all(d % 2 == 0 for d in deg)
            if w and all(d in (0, 2) for d in deg):
                used = {v for v, d in enumerate(deg) if d}
                reached = {next(iter(used))}
                stack = list(reached)
                while stack:
                    u = stack.pop()
                    for v, i in self.adj[u]:
                        if (w >> i) & 1 and v not in reached:
                            reached.add(v)
                            stack.append(v)
                if reached == used:
                    recognized.add(w)
        assert recognized == cycles

        # Every partition has a UNIQUE member containing the first used edge.
        # Hence these recurrences cover all partitions, not just old subunions.
        self.minimum, self.maximum = {0: 0}, {0: 0}
        self.min_choice, self.max_choice = {}, {}
        for w in self.words[1:]:
            i = (w & -w).bit_length() - 1
            candidates = [c for c in self.by_edge[i] if c & w == c]
            assert candidates
            lo = min(candidates, key=lambda c: (self.minimum[w ^ c], c))
            hi = max(candidates, key=lambda c: (self.maximum[w ^ c], -c))
            self.minimum[w] = 1 + self.minimum[w ^ lo]
            self.maximum[w] = 1 + self.maximum[w ^ hi]
            self.min_choice[w], self.max_choice[w] = lo, hi
        self.Q = max(self.minimum.values())
        self.proper_Q = max((self.minimum[w] for w in self.words if w != self.E), default=0)
        self.critical = self.minimum[self.E] > self.proper_Q

    def mask_of_cycle(self, vertices):
        assert len(vertices) >= 3 and len(set(vertices)) == len(vertices)
        answer = sum(1 << self.index[edge(u, v)]
                     for u, v in zip(vertices, vertices[1:] + vertices[:1]))
        assert answer in self.cycle_set
        return answer

    def partition(self, w, maximize=False):
        assert w in self.word_set
        choice = self.max_choice if maximize else self.min_choice
        answer, rem = [], w
        while rem:
            c = choice[rem]
            answer.append(c)
            rem ^= c
        self.check_partition(w, answer)
        assert len(answer) == (self.maximum if maximize else self.minimum)[w]
        return answer

    def check_partition(self, w, parts):
        rem = w
        for c in parts:
            assert c in self.cycle_set and c & rem == c
            rem ^= c
        assert rem == 0

    def primal(self, w, coefficients):
        load = [R(0) for _ in self.edges]
        for c, x in coefficients.items():
            assert c in self.cycle_set and c & w == c and x >= 0
            for i in bits(c):
                load[i] += x
        assert all(load[i] == int(bool((w >> i) & 1)) for i in range(self.m))
        return sum(coefficients.values(), R(0))

    def dual(self, w, prices):
        assert len(prices) == self.m
        for c in self.cycles:
            if c & w == c:
                assert sum((prices[i] for i in bits(c)), R(0)) <= 1
        return sum((prices[i] for i in bits(w)), R(0))

    def cactus_certificate(self, w, q):
        contained = [c for c in self.cycles if c & w == c]
        assert len(contained) == q
        self.check_partition(w, contained)
        prices = [R(0) for _ in self.edges]
        for c in contained:
            prices[(c & -c).bit_length() - 1] = R(1)
        assert self.dual(w, prices) == q
        assert self.primal(w, dict.fromkeys(contained, R(1))) == q
        assert self.minimum[w] == self.maximum[w] == q
        assert max((self.minimum[u] for u in self.words if u != w and u & w == u), default=0) == q - 1
        return prices

    def constant_cycle_dual(self, w):
        """Solve ALL equations y(C)=1 exactly; verify, never infer solvability."""
        active = list(bits(w))
        rows = [[R(int(bool((c >> i) & 1))) for i in active] + [R(1)]
                for c in self.cycles if c & w == c]
        at, pivots = 0, []
        for j in range(len(active)):
            pivot = next((k for k in range(at, len(rows)) if rows[k][j]), None)
            if pivot is None:
                continue
            rows[at], rows[pivot] = rows[pivot], rows[at]
            a = rows[at][j]
            rows[at] = [x / a for x in rows[at]]
            for k in range(len(rows)):
                if k != at and rows[k][j]:
                    a = rows[k][j]
                    rows[k] = [x - a * y for x, y in zip(rows[k], rows[at])]
            pivots.append(j)
            at += 1
        assert all(any(row[:-1]) or row[-1] == 0 for row in rows)
        prices = [R(0) for _ in self.edges]
        for k, j in enumerate(pivots):
            prices[active[j]] = rows[k][-1]
        assert all(sum((prices[i] for i in bits(c)), R(0)) == 1
                   for c in self.cycles if c & w == c)
        assert self.dual(w, prices) == self.minimum[w]
        return prices

    def summary(self):
        transcript = "".join(f"{w:x} {self.minimum[w]} {self.maximum[w]}\n"
                             for w in sorted(self.words))
        return {
            "name": self.name, "vertices": self.n, "edges": self.m,
            "cycle_space_dimension": self.dimension,
            "all_even_restrictions": len(self.words), "all_simple_cycles": len(self.cycles),
            "c": self.minimum[self.E], "maximum_partition_size": self.maximum[self.E],
            "Q": self.Q, "maximum_c_on_proper_even_restrictions": self.proper_Q,
            "critical": self.critical,
            "restriction_counts_by_c": dict(sorted(Counter(self.minimum.values()).items())),
            "cycle_complement_counts_by_c": dict(sorted(Counter(self.minimum[self.E ^ c]
                                                                 for c in self.cycles).items())),
            "all_restriction_min_max_sha256": sha256(transcript.encode()).hexdigest(),
        }

    def dump(self, directory):
        path = directory / (self.name + ".jsonl")
        with path.open("x") as f:
            f.write(json.dumps({"n": self.n, "edges": self.edges, "basis": self.basis}) + "\n")
            for w in self.words:
                f.write(json.dumps({"word": w, "c": self.minimum[w], "nu": self.maximum[w],
                                    "min_first_cycle": self.min_choice.get(w),
                                    "max_first_cycle": self.max_choice.get(w)}) + "\n")


DOUBLED_PAIRS = [(0, 3), (0, 4), (0, 5), (1, 3), (1, 5),
                 (1, 6), (2, 4), (2, 5), (2, 6)]
TRIANGLE = [(3, 4), (3, 6), (4, 6)]


def extension_graph():
    edges, lift = [], []
    for j, (u, v) in enumerate(DOUBLED_PAIRS):
        k = len(edges)
        edges += [(u, v), (u, 7 + j), (7 + j, v)]
        lift += [1 << k, (1 << (k + 1)) | (1 << (k + 2))]
    for uv in TRIANGLE:
        lift.append(1 << len(edges))
        edges.append(uv)
    assert len(lift) == 21 and len(edges) == 30

    def lifted(w):
        return sum(lift[i] for i in bits(w))

    return GraphAudit(16, edges, "extension_counterexample"), lifted, lift


def check_extension():
    a, lift, paths = extension_graph()
    assert (a.minimum[a.E], a.maximum[a.E], a.Q, a.proper_Q) == (4, 10, 6, 6)
    assert len(a.words) == 32768 and len(a.cycles) == 1058
    assert Counter(a.minimum.values()) == {0: 1, 1: 1058, 2: 14876, 3: 13047,
                                          4: 3172, 5: 564, 6: 50}
    assert not a.critical
    assert all(a.minimum[a.E ^ c] == 3 for c in a.cycles)
    # Reconstruct and verify the promised minimum extension for EVERY circuit.
    for c in a.cycles:
        d = [c] + a.partition(a.E ^ c)
        a.check_partition(a.E, d)
        assert len(d) == 4

    minimum_core_masks = [1071185, 566790, 262568, 196608]
    a.check_partition(a.E, [lift(c) for c in minimum_core_masks])
    half_cover_core_masks = [551174, 362644, 659800, 1090722, 1196617, 333345]
    half_cover = {lift(c): R(1, 2) for c in half_cover_core_masks}
    assert a.primal(a.E, half_cover) == 3
    prices = [R(1, 2) if 0 in uv else R(0) for uv in a.edges]
    assert a.dual(a.E, prices) == 3

    # Six doubled edges forming a tree lift to six cactus triangles.
    witness = lift(15615)
    a.cactus_certificate(witness, 6)
    assert witness != a.E
    # Every restriction has cf <= c <= 6; this witness has cf=6. Thus p=6.

    # Literal fractional construction in the general extension/partition lemma.
    maximum = [lift(3 << (2 * j)) for j in range(9)] + [lift(7 << 18)]
    a.check_partition(a.E, maximum)
    coefficients = Counter()
    for c in maximum:
        coefficients.update([c] + a.partition(a.E ^ c))
    coefficients.subtract(maximum)
    assert all(x >= 0 for x in coefficients.values())
    primal = {c: R(x, 9) for c, x in coefficients.items() if x}
    assert a.primal(a.E, primal) == R(10, 3) < 4

    # An extra all-restriction certificate for the marked-splice formula.
    # The mark is the unsplit edge 3--4 (core edge 18, simple edge 27).
    mark = paths[18]
    assert mark.bit_count() == 1
    conditional = []
    for present, core_witness, expected in [(False, 15615, 6), (True, 277749, 5)]:
        subset = [w for w in a.words if bool(w & mark) == present]
        assert max(a.minimum[w] for w in subset) == expected
        w = lift(core_witness)
        assert bool(w & mark) == present
        y = a.constant_cycle_dual(w)
        assert a.dual(w, y) == expected
        a.check_partition(w, a.partition(w))
        conditional.append(expected)
    result = a.summary()
    result.update({"cf": "3", "p": "6", "proper_p_witness_core_mask": 15615,
                   "minimum_partition_core_masks": minimum_core_masks,
                   "half_cover_core_masks": half_cover_core_masks,
                   "extension_subtraction_primal_value": "10/3",
                   "marked_p_absent_present_for_edge_3_4": conditional})
    return a, result


def check_petersen():
    p_edges = {edge(i, (i + 1) % 5) for i in range(5)}
    p_edges |= {edge(i, i + 5) for i in range(5)}
    p_edges |= {edge(5 + i, 5 + (i + 2) % 5) for i in range(5)}
    p_edges = sorted(p_edges)
    assert len(p_edges) == 15
    edges = [(i, j) for i, j in combinations(range(15), 2)
             if set(p_edges[i]) & set(p_edges[j])]
    a = GraphAudit(15, edges, "petersen_line_graph")
    hs = [
        [0, 1, 2, 10, 14, 9, 13, 4, 12, 11, 8, 7, 5, 6, 3],
        [0, 1, 9, 7, 5, 3, 6, 14, 10, 2, 11, 8, 12, 13, 4],
        [0, 2, 1, 7, 9, 13, 14, 6, 10, 11, 12, 8, 5, 3, 4],
        [0, 2, 11, 10, 6, 5, 8, 7, 1, 9, 14, 13, 12, 4, 3],
    ]
    primal = {a.mask_of_cycle(h): R(1, 2) for h in hs}
    assert a.primal(a.E, primal) == 2
    assert a.dual(a.E, [R(1, 15)] * a.m) == 2
    b = a.mask_of_cycle([0, 2, 11, 10, 6, 14, 13, 12, 8, 5, 3, 4])
    t = a.mask_of_cycle([1, 7, 9])
    a.check_partition(a.E, [a.mask_of_cycle(hs[0]), b, t])
    selected = [0, 1, 2, 3, 5, 6, 9]
    triangles = [a.mask_of_cycle([i for i, uv in enumerate(p_edges) if v in uv])
                 for v in selected]
    witness = sum(triangles)
    a.cactus_certificate(witness, 7)
    assert (a.minimum[a.E], a.Q, a.proper_Q) == (3, 7, 7)
    assert len(a.words) == 65536 and not a.critical
    # A local six-triangle cactus avoids line-graph vertex 0 (= Petersen edge 01).
    # Disjoint copies survive in every old Petersen ring after omitting connectors.
    ring_selected = [2, 3, 4, 5, 6, 7]
    ring_triangles = [a.mask_of_cycle([i for i, uv in enumerate(p_edges) if v in uv])
                      for v in ring_selected]
    ring_witness = sum(ring_triangles)
    assert all(0 not in a.edges[i] for i in bits(ring_witness))
    assert ring_witness.bit_count() == 18
    a.cactus_certificate(ring_witness, 6)
    result = a.summary()
    result.update({"cf": "2", "p": "7", "cactus_selected_petersen_vertices": selected,
                   "ring_local_six_triangle_petersen_vertices": ring_selected,
                   "ring_p_lower_bound_by_disjoint_witnesses": "6t for every t>=2",
                   "whole_Petersen_rings_enumerated": False})
    return a, result


# Small exact checks of the algebra in the proved gluing reductions.
# Models carry an all-circuit-tight dual, not a numerical LP solution.
def cycle_model():
    return 3, [(0, 1), (1, 2), (0, 2)], [R(1), R(0), R(0)]


def theta_model(r=2):
    es = [(v, j) for j in range(2, 2 + 2 * r) for v in (0, 1)]
    return 2 + 2 * r, es, [R(1, 2) if u == 0 else R(0) for u, _ in es]


def join_models(A, B, mode, ia=1, ib=1):
    na, ea, ya = A
    nb, eb, yb = B
    if mode == "disjoint":
        return na + nb, ea + [(u + na, v + na) for u, v in eb], ya + yb
    ua, va = edge(*ea[ia])
    ub, vb = edge(*eb[ib])
    if mode in ("vertex", "vertex_edge"):
        rename = {vb: va}
        nxt = na
        for v in range(nb):
            if v != vb:
                rename[v] = nxt
                nxt += 1
    else:
        rename = {v: na + v for v in range(nb)}
        nxt = na + nb
    mapped = [edge(rename[u], rename[v]) for u, v in eb]
    if mode == "vertex":
        return nxt, ea + mapped, ya + yb
    assert mode in ("two_edge", "vertex_edge")
    es = [uv for i, uv in enumerate(ea) if i != ia]
    es += [uv for i, uv in enumerate(mapped) if i != ib]
    ys = [y for i, y in enumerate(ya) if i != ia]
    ys += [y for i, y in enumerate(yb) if i != ib]
    es.append(edge(ua, rename[ub]))
    ys.append(ya[ia] + yb[ib] - 1)
    if mode == "two_edge":
        es.append(edge(va, rename[vb]))
        ys.append(R(0))
    return nxt, es, ys


def check_gluing():
    base = theta_model()
    cases = [("single_cycle", cycle_model(), 1),
             ("two_disjoint_cycles", join_models(cycle_model(), cycle_model(), "disjoint"), 2),
             ("bowtie", join_models(cycle_model(), cycle_model(), "vertex"), 2),
             ("four_path_theta", base, 2),
             ("articulation_sum", join_models(base, base, "vertex"), 4),
             ("two_edge_splice", join_models(base, base, "two_edge"), 3),
             ("vertex_edge_splice", join_models(base, base, "vertex_edge"), 3),
             ("eight_path_theta", theta_model(4), 4)]
    results, audits = [], []
    for name, (n, es, prices), q in cases:
        a = GraphAudit(n, es, name)
        assert a.critical and a.minimum[a.E] == a.maximum[a.E] == q
        assert a.dual(a.E, prices) == q
        assert all(sum((prices[i] for i in bits(c)), R(0)) == 1 for c in a.cycles)
        # Restrict the SAME signed prices to every even word.
        for w in a.words:
            assert sum((prices[i] for i in bits(w)), R(0)) == a.minimum[w] == a.maximum[w]
        if "splice" in name:
            assert min(prices) < 0
        results.append({**a.summary(), "cf": str(q), "p": str(q),
                        "signed_dual": list(map(str, prices))})
        audits.append(a)
    # For the theta mark (edge index 1), the two marked maxima are 1 and 2.
    theta = audits[3]
    marked = [max(theta.minimum[w] for w in theta.words if bool(w & 2) == b)
              for b in (False, True)]
    assert marked == [1, 2]
    for a in audits[5:7]:
        assert a.Q == max(marked[0] + marked[0], marked[1] + marked[1] - 1) == 3
    return audits, results


def diagnose_maximum_critical(a):
    """The user's maximum-Q/minimum-support reduction, with exact certificates.

    This is a per-input diagnostic, never a universal assertion. If a selected
    critical restriction had nonconstant partition count, the positive result
    would include an exact fractional primal and a bound on EVERY restriction.
    """
    q = a.Q
    if q == 0:
        return {"ambient_p": "0", "ambient_Q": 0, "critical_word": 0}
    w = next(w for w in a.words if a.minimum[w] == q)
    subwords = [u for u in a.words if u & w == u]
    proper = max(a.minimum[u] for u in subwords if u != w)
    assert proper == q - 1
    s = a.maximum[w]
    result = {"ambient_Q": q, "critical_word_in_ambient_edge_indices": w,
              "critical_edges": [a.edges[i] for i in bits(w)],
              "all_even_restrictions_of_critical_word": len(subwords),
              "critical_c": q, "critical_nu": s, "proper_c_upper": proper}
    if s == q:
        prices = a.constant_cycle_dual(w)
        assert a.dual(w, prices) == q
        result.update({"ambient_p": str(q), "equality_certified_on_this_input": True,
                       "critical_dual_in_ambient_edge_indices": list(map(str, prices))})
    else:
        assert s > q
        P = a.partition(w, maximize=True)
        coefficients = Counter()
        for c in P:
            assert a.minimum[w ^ c] == q - 1
            coefficients.update([c] + a.partition(w ^ c))
        coefficients.subtract(P)
        assert all(x >= 0 for x in coefficients.values())
        primal = {c: R(x, s - 1) for c, x in coefficients.items() if x}
        bound = R(s * (q - 1), s - 1)
        assert a.primal(w, primal) == bound < q
        assert proper <= bound
        result.update({"counterexample_to_c_le_p_ON_THE_CRITICAL_RESTRICTION": True,
                       "critical_cf_upper": str(bound), "critical_p_upper": str(bound),
                       "critical_primal_in_ambient_cycle_masks":
                           {str(c): str(x) for c, x in sorted(primal.items())}})
    return result


def protected_snapshot():
    root = Path(__file__).resolve().parent
    omitted = {Path(__file__).name, "ResearchCriticalGraphic.md"}
    return {str(p): sha256(p.read_bytes()).hexdigest()
            for folder in (root, root.parent / "newSubmission") if folder.exists()
            for p in folder.rglob("*") if p.is_file() and p.name not in omitted}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dump-restrictions", type=Path)
    parser.add_argument("--graph-json", type=Path,
                        help='additional small even simple graph: {"n": ..., "edges": [[u,v], ...]}')
    args = parser.parse_args()
    spec = Path(__file__).with_name("Spec.lean")
    assert sha256(spec.read_bytes()).hexdigest() == SPEC_SHA256
    before = protected_snapshot()
    extension, extension_result = check_extension()
    print("Checked all 32,768 even restrictions of the simple extension counterexample.", flush=True)
    petersen, petersen_result = check_petersen()
    print("Checked all 65,536 even restrictions of the Petersen line graph.", flush=True)
    toy_audits, toy_results = check_gluing()
    all_audits = [extension, petersen] + toy_audits
    extra = {}
    extracted = {a.name: diagnose_maximum_critical(a) for a in [extension, petersen]}
    if args.graph_json:
        data = json.loads(args.graph_json.read_text())
        supplied = GraphAudit(data["n"], data["edges"], "supplied_graph")
        all_audits.append(supplied)
        extra = {"graph": supplied.summary(), "diagnostic": diagnose_maximum_critical(supplied)}
    if args.dump_restrictions:
        args.dump_restrictions.mkdir(parents=True, exist_ok=False)
        for a in all_audits:
            a.dump(args.dump_restrictions)
    assert before == protected_snapshot(), "A protected file changed during execution"
    result = {"method": "complete cycle-space enumeration, exact min/max DP, rational primal/dual checks",
              "protected_spec_sha256": SPEC_SHA256,
              "protected_files_unchanged_during_check": len(before),
              "extension_counterexample_NOT_c_critical": extension_result,
              "petersen_hereditary_certificate": petersen_result,
              "critical_gluing_certificates": toy_results,
              "maximum_Q_critical_extractions": extracted,
              "additional_supplied_graph": extra,
              "universal_graphic_c_le_p_proved": False,
              "universal_graphic_c_le_2p_proved": False,
              "counterexample_to_either_universal_target_claimed":
                  bool(extra.get("diagnostic", {}).get(
                      "counterexample_to_c_le_p_ON_THE_CRITICAL_RESTRICTION", False))}
    print(json.dumps(result, indent=2, sort_keys=True))
    print("ALL EXACT CHECKS PASSED")


if __name__ == "__main__":
    main()
