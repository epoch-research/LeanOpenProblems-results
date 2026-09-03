#!/usr/bin/env python3
"""Exact finite audits for CubeHigherBlockCapacity.md.

These check identities and finite algebra used in the paper proof.  They do
not search for Ramsey counterexamples and do not prove the missing outer-
cube conditioning step.  No external packages or Lean axioms are used.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import comb, prod
from pathlib import Path
import hashlib


SPEC_HASH = "9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b"


def cube_edges(k):
    return [(x, x ^ (1 << i)) for x in range(1 << k)
            for i in range(k) if not (x >> i) & 1]


def graph(n, edges):
    a = [[False] * n for _ in range(n)]
    for x, y in edges:
        assert x != y
        a[x][y] = a[y][x] = True
    return a


def maps(n, source_vertices, edges, a, injective=False):
    """Backtracking, with original source labels retained."""
    labels = list(source_vertices)
    previous = {x: [] for x in labels}
    order = {x: i for i, x in enumerate(labels)}
    for x, y in edges:
        if order[x] > order[y]:
            x, y = y, x
        previous[y].append(x)
    assignment = {}
    used = set()

    def rec(j):
        if j == len(labels):
            yield tuple(assignment[x] for x in labels)
            return
        x = labels[j]
        for v in range(n):
            if injective and v in used:
                continue
            if any(not a[v][assignment[y]] for y in previous[x]):
                continue
            assignment[x] = v
            if injective:
                used.add(v)
            yield from rec(j + 1)
            if injective:
                used.remove(v)
            del assignment[x]

    yield from rec(0)


def weighted_count(n, vertices, edges, a, u, injective=False):
    return sum(prod(u[v] for v in f)
               for f in maps(n, vertices, edges, a, injective))


def cube_count(k, a, u, injective=False):
    return weighted_count(len(a), range(1 << k), cube_edges(k),
                          a, u, injective)


def packings(k, s, a):
    b = 1 << k
    edges = [(i*b+x, i*b+y) for i in range(s) for x, y in cube_edges(k)]
    yield from maps(len(a), range(s*b), edges, a, True)


def audit_norm_and_deletion():
    n = 4
    all_edges = list(combinations(range(n), 2))
    tests = 0
    roots = 0
    for mask in range(1 << len(all_edges)):
        a = graph(n, [e for i, e in enumerate(all_edges) if mask >> i & 1])
        for u in ([1]*n, [1, 2, 3, 2]):
            W = sum(u)
            alpha = F(max(u), W)
            p = F(sum(u[x]*u[y] for x in range(n) for y in range(n)
                      if a[x][y]), W**2)
            previous_t = None
            previous_e = None
            for k in (1, 2, 3):
                b = 1 << k
                edges = cube_edges(k)
                e = len(edges)
                fs = list(maps(n, range(b), edges, a))
                weights = [prod(u[v] for v in f) for f in fs]
                H = sum(weights)
                I = sum(w for f, w in zip(fs, weights) if len(set(f)) == b)
                t = F(H, W**b)
                assert t >= p**e
                if previous_t is not None:
                    assert t**previous_e >= previous_t**e
                remaining = list(range(1, b))
                deleted_edges = [(x, y) for x, y in edges if x != 0 and y != 0]
                Hd = weighted_count(n, remaining, deleted_edges, a, u)
                td = F(Hd, W**(b-1))
                assert td**e <= t**(e-k)
                assert F(I, W**b) >= t - comb(b, 2)*alpha*td
                for v in range(n):
                    pin = F(sum(w for f, w in zip(fs, weights) if f[0] == v), W**b)
                    assert pin <= F(u[v], W)*td
                for x, y in combinations(range(b), 2):
                    collision = F(sum(w for f, w in zip(fs, weights)
                                      if f[x] == f[y]), W**b)
                    assert collision <= alpha*td
                    roots += 1
                previous_t, previous_e = t, e
                tests += 1
            # All-source-subset deletion inequality, not only one pinned label.
            k, b, e = 2, 4, 4
            edges = cube_edges(k)
            fs = list(maps(n, range(b), edges, a, True))
            t = F(cube_count(k, a, u), W**b)
            for bits in range(1 << b):
                S = [x for x in range(b) if bits >> x & 1]
                T = [x for x in range(b) if not bits >> x & 1]
                rem_edges = [(x, y) for x, y in edges if x in T and y in T]
                tr = F(weighted_count(n, T, rem_edges, a, u), W**len(T))
                assert tr**e <= t**len(rem_edges)
                by_pin = defaultdict(int)
                for f in fs:
                    by_pin[tuple(f[x] for x in S)] += prod(u[v] for v in f)
                for pin, mass in by_pin.items():
                    assert F(mass, W**b) <= prod(F(u[v], W) for v in pin)*tr
                    roots += 1
    print(f"Weighted norm/Sidorenko/deletion audits: {tests}; collision and pin audits: {roots}")


def audit_auxiliary_identity():
    cases = 0
    for n, k in ((4, 1), (8, 2)):
        if n == 4:
            edges = list(combinations(range(n), 2))
            hosts = [graph(n, [e for i, e in enumerate(edges) if mask >> i & 1])
                     for mask in range(1 << len(edges))]
        else:
            hosts = [graph(n, combinations(range(n), 2)),
                     graph(n, [(x, y) for x in range(4) for y in range(4, 8)]),
                     graph(n, cube_edges(3)),
                     graph(n, [e for e in combinations(range(n), 2)
                               if (e[0] + 2*e[1]) % 5 != 0])]
        for a in hosts:
            u = [1 + i % 3 for i in range(n)]
            b = 1 << k
            vertices = set(range(n))
            aux_edges = 0
            disjoint_pairs = 0
            for f in maps(n, range(b), cube_edges(k), a, True):
                wf = prod(u[v] for v in f)
                for g in permutations(vertices - set(f), b):
                    if not all(a[g[x]][g[y]] for x, y in cube_edges(k)):
                        continue
                    weight = wf*prod(u[v] for v in g)
                    disjoint_pairs += weight
                    if all(a[f[x]][g[x]] for x in range(b)):
                        aux_edges += weight
                        # Literal coordinate-preserving lift, including mixed squares.
                        h = f + g
                        assert len(set(h)) == 2*b
                        assert all(a[h[x]][h[y]] for x, y in cube_edges(k+1))
                        for x in range(2*b):
                            for i, j in combinations(range(k+1), 2):
                                square = (x, x ^ (1 << i),
                                          x ^ (1 << i) ^ (1 << j), x ^ (1 << j))
                                assert all(a[h[square[l]]][h[square[(l+1) % 4]]]
                                           for l in range(4))
            assert aux_edges == cube_count(k+1, a, u, True)
            assert disjoint_pairs == sum(prod(u[v] for v in f) for f in packings(k, 2, a))
            assert disjoint_pairs <= cube_count(k, a, u)**2
            cases += 1
    print(f"Exact weighted auxiliary-edge and disjoint-pair identities: {cases} hosts")


def audit_integral_gibbs():
    # Nontrivial exact KKT example.  This audits finite convex algebra;
    # its small parameters are not the asymptotic theorem's hypotheses.
    n, k, s = 7, 1, 2
    a = graph(n, list(combinations(range(6), 2)) + [(0, 6)])
    ps = list(packings(k, s, a))
    assert len(ps) == 440
    w = [F(3, 4)] + [F(1)]*6
    masses = [prod(w[v] for v in f) for f in ps]
    Z = sum(masses)
    occ = [sum(m for f, m in zip(ps, masses) if v in f)/Z for v in range(n)]
    assert Z == 360
    assert occ == [F(2, 3)] + [F(19, 30)]*5 + [F(1, 6)]
    c = F(2, 3)
    assert occ[0] == c and all(x < c for x in occ[1:])
    assert sum(occ) == 4
    for label in range(4):
        for v in range(n):
            pin = sum(m for f, m in zip(ps, masses) if f[label] == v)/Z
            assert pin == occ[v]/4
            assert pin <= c/4
    # An explicit strict feasible law, independently of the minimizer.
    w0 = [F(2, 3)] + [F(1)]*6
    m0 = [prod(w0[v] for v in f) for f in ps]
    Z0 = sum(m0)
    assert max(sum(m for f, m in zip(ps, m0) if v in f)/Z0
               for v in range(n)) == F(16, 25) < c
    assert sum(1 for f in ps if 0 not in f) == 120 <= Z

    # Conditional product-weight law: freeze one of three actual blocks.
    n, k, s = 8, 1, 3
    a = graph(n, [e for e in combinations(range(n), 2)
                  if (e[0]+2*e[1]) % 5 != 0])
    w = [F(3, 4), F(1, 2)] + [F(1)]*6
    grouped = defaultdict(list)
    for f in packings(k, s, a):
        grouped[f[:2]].append((f[2:], prod(w[v] for v in f[2:])))
    for frozen, options in grouped.items():
        residual = [v for v in range(n) if v not in frozen]
        ar = [[a[x][y] for y in residual] for x in residual]
        wr = [w[v] for v in residual]
        denominator = sum(m for f, m in options)
        direct = sum(prod(wr[v] for v in f) for f in packings(1, 2, ar))
        numerator = sum(m for f, m in options if a[f[0]][f[2]] and a[f[1]][f[3]])
        assert denominator == direct
        assert numerator == cube_count(2, ar, wr, True)
        assert denominator <= cube_count(1, ar, wr)**2
    print(f"Integral entropy/KKT law: 440 configurations; conditional pair laws: {len(grouped)}")


def falling(n, r):
    return prod(n-i for i in range(r)) if 0 <= r <= n else 0


def audit_patch_formulas_and_constants():
    # Complete bipartite hosts give exact all-order patch probabilities.
    patches = 0
    side = 1 << 16
    for k in range(1, 5):
        b = 1 << k
        for ell in range(1, 5):
            L = 1 << ell
            original_per_part = L*b//2
            common = falling(side, original_per_part)**2
            Z_L = 2**L * common
            I_patch = 2 * common
            assert F(I_patch, Z_L) == F(1, 2**(L-1))
            assert F(I_patch, Z_L) >= F(1, 2)**(b*ell*L//2)
            patches += 1

    # The constants used to prove the asymptotic estimates are exact integers.
    assert 32**8 < 2**9*15**8              # rho >= 15/32 > 2^(-9/8)
    assert 2**25 < 9**8                   # 2^(25/8) < 9
    assert 9**32 < 2**7*8**32             # ratio monotonicity of d*2^(-7d/32)
    assert 288*512 <= 63*4096              # eta_(k+1) coefficient
    assert F(1, 128) + F(1, 4096) <= F(1, 64)
    assert (F(63, 64))**32 >= F(1, 2)
    for d in range(8, 4097):
        k = d//4
        assert F(9*k, 16) - F(d, 8) >= F(d, 64)-F(9, 16)
        N = 4096*(1 << d)
        sigma = F(1, 128) + F(1, 4096)
        p = F(N-1, 2*N)
        assert p-2*sigma >= F(15, 32)
        assert 1-sigma >= F(63, 64)
        assert F(1, 4096) <= F(1, 256)
        if d >= 40:
            J = (3*d)//10
            assert J >= k+1
            assert F(25*J, 8)-d <= -F(d, 16)
    # Exact finite-population condition for the elementary two-root DRC lemma.
    for r in range(6, 129):
        m = 1 << (r-1)
        assert r*(r-1) <= m
        assert F(m**r, falling(m, r)) <= 2
    print(f"All-order cube-patch formula audits: {patches}; exact constant/rounding checks: 4089 dimensions")


def main():
    spec = Path(__file__).with_name("Spec.lean")
    before = hashlib.sha256(spec.read_bytes()).hexdigest()
    assert before == SPEC_HASH
    audit_norm_and_deletion()
    audit_auxiliary_identity()
    audit_integral_gibbs()
    audit_patch_formulas_and_constants()
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_HASH
    print("Spec.lean SHA-256:", SPEC_HASH)
    print("PASS: exact identities and proof constants checked.")
    print("NOT CLAIMED: outer-cube conditioning, a red/blue augmentation theorem, or R(Q_d)=O(2^d).")


if __name__ == "__main__":
    main()
