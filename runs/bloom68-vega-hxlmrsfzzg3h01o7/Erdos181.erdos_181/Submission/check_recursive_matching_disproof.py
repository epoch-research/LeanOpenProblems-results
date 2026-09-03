#!/usr/bin/env python3
"""Finite checks and a kernel-checkable Lean certificate for the matching investigation.

The infinite family is proved in CubeRecursiveMatchingDisproof.md, not by finite tests.
Default checks use only the Python standard library. --milp is an independent SciPy check.
--write-lean regenerates the marked finite-certificate section of the companion Lean file.
"""
from argparse import ArgumentParser
from collections import deque
from fractions import Fraction
from itertools import product
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
PERMS = [
    [0],
    [0, 1],
    [0, 1, 3, 2],
    [2, 3, 4, 5, 6, 7, 0, 1],
    [0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13, 14, 15, 8, 9],
]
FOUR_COLORS = [
    0, 1, 1, 2, 1, 0, 0, 2, 1, 0, 2, 3, 2, 1, 0, 3,
    1, 3, 2, 0, 0, 2, 2, 1, 1, 0, 0, 2, 0, 1, 1, 3,
]
SPEC_HASH = "9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b"


def double(edges, p):
    n = len(p)
    assert sorted(p) == list(range(n))
    return edges + [(u + n, v + n) for u, v in edges] + [
        (u, n + p[u]) for u in range(n)
    ]


def adjacency(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        assert u != v and 0 <= u < n and 0 <= v < n
        assert v not in adj[u]
        adj[u].add(v)
        adj[v].add(u)
    return adj


def enumerate_colorings(n, edges, k):
    """Exhaustive domain-propagating search; fix color(0)=0, then restore symmetry."""
    adj = adjacency(n, edges)

    def propagate(dom, queue):
        while queue:
            v = queue.pop()
            c = dom[v]
            assert c and c.bit_count() == 1
            for w in sorted(adj[v]):
                if dom[w] & c:
                    dom[w] ^= c
                    if not dom[w]:
                        return False
                    if dom[w].bit_count() == 1:
                        queue.append(w)
        return True

    def search(dom):
        undecided = [v for v in range(n) if dom[v].bit_count() > 1]
        if not undecided:
            f = tuple(d.bit_length() - 1 for d in dom)
            assert all(f[u] != f[v] for u, v in edges)
            yield f
            return
        v = min(undecided, key=lambda v: (
            dom[v].bit_count(), -sum(dom[w].bit_count() > 1 for w in adj[v]), v
        ))
        bits = dom[v]
        while bits:
            bit = bits & -bits
            bits ^= bit
            child = dom.copy()
            child[v] = bit
            if propagate(child, [v]):
                yield from search(child)

    dom = [(1 << k) - 1] * n
    dom[0] = 1
    if not propagate(dom, [0]):
        return []
    out = [tuple((c + shift) % k for c in f)
           for f in search(dom) for shift in range(k)]
    assert len(set(out)) == len(out)
    return out


def check_cyclic_count_step(colorings, h, m):
    shifts = list(product(range(h), repeat=m))
    counts = {s: 0 for s in shifts}
    aggregate = 0
    for f in colorings:
        for g in colorings:
            allowed = []
            for b in range(m):
                assert set(f[b*h:(b+1)*h]) == set(range(3))
                assert set(g[b*h:(b+1)*h]) == set(range(3))
                good = [s for s in range(h)
                        if all(f[b*h+x] != g[b*h+(x+s) % h] for x in range(h))]
                assert len(good) <= h - 1
                allowed.append(good)
            compatible = list(product(*allowed))
            assert len(compatible) <= (h - 1) ** m
            aggregate += len(compatible)
            for s in compatible:
                counts[s] += 1
    assert aggregate == sum(counts.values())
    assert aggregate <= len(colorings) ** 2 * (h - 1) ** m
    assert min(counts.values()) * h**m <= aggregate
    return counts


def lean_certificate(edges):
    """Emit a short elementary case proof: no solver/native axioms enter Lean."""
    n = 32
    adj = adjacency(n, edges)
    lines = []
    decisions = 0

    def emit(depth, line):
        lines.append("  " * depth + line)

    def excluded(v, color, neighbor):
        return (f"(by simpa only [h{neighbor}] using "
                f"c.valid (show exampleGraph.Adj {v} {neighbor} from by decide))")

    def search(assigned, depth):
        nonlocal decisions
        assigned = assigned.copy()
        while True:
            for u, v in edges:
                if u in assigned and v in assigned and assigned[u] == assigned[v]:
                    emit(depth, f"exact (c.valid (show exampleGraph.Adj {u} {v} "
                         f"from by decide)) (h{u}.trans h{v}.symm)")
                    return
            available = {}
            witnesses = {}
            for v in range(n):
                if v in assigned:
                    continue
                forbidden = {}
                for w in sorted(adj[v]):
                    if w in assigned:
                        forbidden.setdefault(assigned[w], w)
                witnesses[v] = forbidden
                available[v] = [c for c in range(3) if c not in forbidden]
                if not available[v]:
                    emit(depth, "exact fin3_impossible " + " ".join(
                        excluded(v, c, forbidden[c]) for c in range(3)))
                    return
            forced = next((v for v in sorted(available) if len(available[v]) == 1), None)
            if forced is None:
                break
            color = available[forced][0]
            forbidden = witnesses[forced]
            emit(depth, f"have h{forced} : c {forced} = {color} := fin3_force{color} " +
                 " ".join(excluded(forced, a, forbidden[a])
                          for a in range(3) if a != color))
            assigned[forced] = color
        if not available:
            raise AssertionError("A valid 3-coloring was found while generating an UNSAT proof")
        decisions += 1
        v = min(available, key=lambda v: (
            len(available[v]), -sum(w not in assigned for w in adj[v]), v
        ))
        opts = available[v]
        if len(opts) == 3:
            emit(depth, f"rcases fin3_options (c {v}) with h{v} | h{v} | h{v}")
        else:
            assert len(opts) == 2
            omitted = next(c for c in range(3) if c not in opts)
            emit(depth, f"rcases fin3_options{omitted} " +
                 excluded(v, omitted, witnesses[v][omitted]) + f" with h{v} | h{v}")
        for color in opts:
            emit(depth, "·")
            search({**assigned, v: color}, depth + 1)

    search({}, 1)
    return lines, decisions


def write_lean(edges):
    path = ROOT / "CubeRecursiveMatchingVerification.lean"
    marker = "-- BEGIN GENERATED FINITE CERTIFICATE"
    text = path.read_text()
    prefix = text.split(marker)[0] if marker in text else text.rsplit(
        "end CubeRecursiveMatchingVerification", 1)[0]
    parts = [marker, "set_option maxRecDepth 8192", "set_option maxHeartbeats 4000000", "",
             "/-- The exact five recursive perfect matchings in the 32-vertex example. -/",
             "def examplePermutations : List (List ℕ) := " + str(PERMS), "",
             "def doubleEdges (edges : List (ℕ × ℕ)) (p : List ℕ) : List (ℕ × ℕ) :=",
             "  edges ++ edges.map (fun e => (e.1 + p.length, e.2 + p.length)) ++",
             "    p.zipIdx.map (fun e => (e.2, p.length + e.1))", "",
             "def exampleEdges : List (ℕ × ℕ) := examplePermutations.foldl doubleEdges []", "",
             "def exampleGraph : SimpleGraph (Fin 32) :=",
             "  SimpleGraph.fromRel fun x y => (x.val, y.val) ∈ exampleEdges", "",
             "instance : DecidableRel exampleGraph.Adj := by",
             "  unfold exampleGraph", "  infer_instance", "",
             "theorem example_permutations_valid :",
             "    examplePermutations.all (fun p => decide (p.Perm (List.range p.length))) = true := by",
             "  decide", "",
             "theorem example_permutation_sizes :",
             "    examplePermutations.map List.length = [1, 2, 4, 8, 16] := by decide", "",
             "theorem example_degree : ∀ v : Fin 32, exampleGraph.degree v = 5 := by decide", ""]
    parts += ["private theorem fin3_options (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by",
              "  fin_cases x <;> simp", ""]
    for color in range(3):
        other = [c for c in range(3) if c != color]
        parts += [f"private theorem fin3_options{color} {{x : Fin 3}} (h : x ≠ {color}) :",
                  f"    x = {other[0]} ∨ x = {other[1]} := by",
                  "  fin_cases x <;> simp_all", "",
                  f"private theorem fin3_force{color} {{x : Fin 3}} " +
                  " ".join(f"(h{a} : x ≠ {a})" for a in other) + f" : x = {color} := by",
                  "  fin_cases x <;> simp_all", ""]
    parts += ["private theorem fin3_impossible {x : Fin 3} (h0 : x ≠ 0) (h1 : x ≠ 1)",
              "    (h2 : x ≠ 2) : False := by", "  fin_cases x <;> simp_all", "",
              "/-- An elementary finite case proof, generated and then checked by the Lean kernel. -/",
              "theorem example_not_colorable_three : ¬ exampleGraph.Colorable 3 := by",
              "  rintro ⟨c⟩"]
    cert, decisions = lean_certificate(edges)
    parts += cert + ["", "def exampleFourColors : Fin 32 → Fin 4 := ![" +
                     ", ".join(map(str, FOUR_COLORS)) + "]", "",
                     "theorem example_colorable_four : exampleGraph.Colorable 4 := by",
                     "  exact ⟨SimpleGraph.Coloring.mk exampleFourColors (by decide)⟩", "",
                     "theorem example_chromatic_number : exampleGraph.chromaticNumber = 4 := by",
                     "  exact (SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable).2",
                     "    ⟨example_colorable_four, example_not_colorable_three⟩", "",
                     "theorem example_connected : exampleGraph.Connected := by",
                     "  have h0 : exampleGraph.Reachable 0 0 := .rfl"]
    adj = adjacency(32, edges)
    for v in range(1, 32):
        w = min(w for w in adj[v] if w < v)
        parts.append(f"  have h{v} : exampleGraph.Reachable 0 {v} := h{w}.trans "
                     f"(show exampleGraph.Adj {w} {v} from by decide).reachable")
    parts += ["  apply (SimpleGraph.connected_iff_exists_forall_reachable _).2",
              "  refine ⟨0, ?_⟩", "  intro v", "  fin_cases v <;> assumption", "",
              "/-- The explicit example has a countercoloring on 3*31 = 93 vertices. -/",
              "theorem example_countercoloring_93 :",
              "    ∃ R : SimpleGraph (Fin 3 × Fin 31),",
              "      ¬ exampleGraph.IsContained R ∧ ¬ exampleGraph.IsContained Rᶜ := by",
              "  simpa using multipartite_countercoloring exampleGraph example_connected 3",
              "    example_not_colorable_three", "",
              "#print axioms multipartite_countercoloring",
              "#print axioms example_not_colorable_three",
              "#print axioms example_chromatic_number",
              "#print axioms example_connected",
              "#print axioms example_degree",
              "#print axioms example_countercoloring_93", "",
              "-- END GENERATED FINITE CERTIFICATE", "end CubeRecursiveMatchingVerification", ""]
    path.write_text(prefix + "\n".join(parts))
    print(f"Generated Lean finite certificate: {decisions} case splits, {len(cert)} proof lines")


def milp_check(n, edges):
    import numpy as np
    from scipy.optimize import milp, LinearConstraint, Bounds
    from scipy.sparse import lil_matrix
    k = 3
    A = lil_matrix((n + k * len(edges), n * k), dtype=float)
    lo = np.zeros(A.shape[0])
    hi = np.ones(A.shape[0])
    lo[:n] = 1
    for v in range(n):
        A[v, v*k:(v+1)*k] = 1
    for j, (u, v) in enumerate(edges):
        for c in range(k):
            A[n+j*k+c, [u*k+c, v*k+c]] = 1
    res = milp(c=np.zeros(n*k), integrality=np.ones(n*k), bounds=Bounds(0, 1),
               constraints=LinearConstraint(A.tocsr(), lo, hi), options={"time_limit": 60})
    assert res.status == 2, res.message
    print("Independent HiGHS MILP confirms no proper 3-coloring:", res.message)


def main():
    ap = ArgumentParser()
    ap.add_argument("--write-lean", action="store_true")
    ap.add_argument("--milp", action="store_true")
    args = ap.parse_args()
    assert hashlib.sha256((ROOT / "Spec.lean").read_bytes()).hexdigest() == SPEC_HASH
    levels = [([], 1)]
    for d, p in enumerate(PERMS, 1):
        old, n = levels[-1]
        assert len(p) == n == 2**(d-1)
        edges = double(old, p)
        n *= 2
        adj = adjacency(n, edges)
        assert len(edges) == d*n//2
        assert all(len(a) == d for a in adj)
        assert all(not (adj[u] & adj[v]) for u, v in edges)
        reached = {0}
        queue = deque([0])
        while queue:
            for w in adj[queue.popleft()]:
                if w not in reached:
                    reached.add(w)
                    queue.append(w)
        assert len(reached) == n
        levels.append((edges, n))
    print("All five levels: identical halves, perfect matching, connected, triangle-free, d-regular")
    cols = {}
    for d, expected in [(3, 48), (4, 72), (5, 0)]:
        es, n = levels[d]
        cols[d] = enumerate_colorings(n, es, 3)
        assert len(cols[d]) == expected
        print(f"Dimension {d}: {n} vertices, {expected} labelled proper 3-colorings")
    counts1 = check_cyclic_count_step(cols[3], 8, 1)
    assert [counts1[(s,)] for s in range(8)] == [432, 120, 72, 120, 432, 120, 72, 120]
    assert counts1[(2,)] == len(cols[4]) == min(counts1.values())
    counts2 = check_cyclic_count_step(cols[4], 8, 2)
    assert counts2[(0, 2)] == len(cols[5]) == 0
    print("Exact double-counting checked for every pair of half-colorings and every cyclic matching")
    print("8 -> 16 counts:", [counts1[(s,)] for s in range(8)])
    print("16 -> 32: 64 shift vectors; sum of coloring counts =", sum(counts2.values()),
          "; zero-count choices =", sum(v == 0 for v in counts2.values()))
    edges, n = levels[5]
    assert len(FOUR_COLORS) == n and set(FOUR_COLORS) == set(range(4))
    assert all(FOUR_COLORS[u] != FOUR_COLORS[v] for u, v in edges)
    print("Explicit proper 4-coloring checked")
    for h in range(2, 12):
        assert Fraction(h-1, h)**(h-1) <= Fraction(1, 2)
        for k in range(2, 12):
            assert k < 2**k
    for j in range(1, 100):
        assert 2*(j*2**(j-1)) + 2**j == (j+1)*2**j
    print("Rational amplification inequalities and exact exponent identity checked on test ranges")
    out = {"dimension": 5, "vertices": n, "permutations": PERMS,
           "edges": edges, "three_coloring_counts": [48, 72, 0],
           "four_coloring": FOUR_COLORS}
    (ROOT / "RecursiveMatchingExample32.json").write_text(json.dumps(out, indent=2) + "\n")
    if args.write_lean:
        write_lean(edges)
    if args.milp:
        milp_check(n, edges)
    assert hashlib.sha256((ROOT / "Spec.lean").read_bytes()).hexdigest() == SPEC_HASH
    print("Spec.lean hash unchanged:", SPEC_HASH)
    print("PASS (infinite-family conclusions rely on the accompanying paper proof)")


if __name__ == "__main__":
    main()
