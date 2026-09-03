#!/usr/bin/env python3
"""Exact audits for CubeConflictDRCAttempt.md; not a Ramsey proof.

No large-host adjacency matrix is constructed.  The k=4, s=3 test uses
bit-vector symplectic arithmetic on a host of order 2^22, and constructs
an actual injective auxiliary Q_13 with repeated ORIGINAL vertices.
"""
from collections import Counter, deque
from fractions import Fraction
from itertools import product
from math import prod
from pathlib import Path
import hashlib


def bilinear_factory(n):
    low = sum(1 << i for i in range(0, n, 2))

    def B(x, y):
        return (((x & low) & (y >> 1)).bit_count()
                + (((x >> 1) & (y & low)).bit_count())) & 1
    return B


def quadratic(a, k):
    return (sum(((a >> i) & 1) * ((a >> (i + 1)) & 1)
                for i in range(0, k, 2)) + a.bit_count()) & 1


def cube_edges(k):
    for a in range(1 << k):
        for i in range(k):
            if not (a >> i) & 1:
                yield a, a ^ (1 << i)


def binary_rank(vectors):
    basis = {}
    for v in vectors:
        while v:
            j = v.bit_length() - 1
            if j in basis:
                v ^= basis[j]
            else:
                basis[j] = v
                break
    return len(basis)


def orbit(seed, generators):
    seen = {seed}
    todo = deque([seed])
    while todo:
        x = todo.popleft()
        for f in generators:
            y = f(x)
            if y not in seen:
                seen.add(y)
                todo.append(y)
    return seen


def audit_small_symmetry():
    n, N = 4, 16
    B = bilinear_factory(n)
    vertices = set(range(1, N))
    oriented = {(x, y) for x in range(N) for y in range(N) if B(x, y)}
    assert len(oriented) == N * (N - 1) // 2
    for x in vertices:
        assert sum(B(x, y) for y in range(N)) == N // 2
    for a in vertices:
        tr = lambda x, a=a: x ^ (a if B(x, a) else 0)
        assert {tr(x) for x in range(N)} == set(range(N))
        assert all(B(tr(x), tr(y)) == B(x, y)
                   for x in range(N) for y in range(N))
    vgens = [(lambda x, a=a: x ^ (a if B(x, a) else 0)) for a in vertices]
    egens = [(lambda xy, a=a: (xy[0] ^ (a if B(xy[0], a) else 0),
                              xy[1] ^ (a if B(xy[1], a) else 0)))
             for a in vertices]
    assert orbit(1, vgens) == vertices
    assert orbit((1, 2), egens) == oriented
    # The exact strict KKT/Jensen slopes used both for small-cube edge
    # fugacity and for the simultaneous vertex/edge budget calculation.
    K = 64
    alpha = Fraction(2 * K, N * N)
    assert alpha > Fraction(4, N * (N - 1))
    assert Fraction(2, N * (N - 1)) <= Fraction(K, N * N)
    print("PASS: symplectic transvections preserve all 256 pairings;"
          " nonzero-vertex orbit 15, oriented-edge orbit 120.")


def audit_root_counting_lemma():
    # Exhaust the small k=2 version of the rank/affine completion argument
    # used to lower-bound the FULL two-root neighborhood in the report.
    k, b, udim, m = 2, 4, 6, 64
    B = bilinear_factory(udim)
    good = 0
    systems = 0
    for u0 in range(m):
        for u1 in range(m):
            if binary_rank([u0, u1]) < k:
                continue
            good += 1
            solutions = {(i, j): {v for v in range(m)
                                   if B(v, u0) == i and B(v, u1) == j}
                         for i in range(2) for j in range(2)}
            assert all(len(S) == m // b for S in solutions.values())
            systems += len(solutions)
            for S in solutions.values():
                first = min(S - {0, u0, u1})
                for S2 in solutions.values():
                    assert len(S2 - {0, u0, u1, first}) >= b*b - b
    assert good == (m - 1) * (m - 2) == 3906
    assert Fraction(good, m*m) >= 1 - Fraction(5, 8*b)
    assert (1 - Fraction(1, b)) ** (b // 2) >= Fraction(1, 2)
    print(f"PASS: full-root-neighborhood counting lemma: all {m*m} "
          f"small parity assignments, {good} good; {systems} affine "
          "right-hand sides have exactly 16 solutions and valid avoidance counts.")


def audit_concrete_auxiliary():
    k, s = 4, 3
    d, r = 4 * k + 1, 3 * k + 1
    b, m = 1 << k, 1 << (3 * k)
    n = 4 * k + 2 * s
    N, D = 1 << n, 1 << (2 * s)
    B = bilinear_factory(n)
    udim = 3 * k
    toffset = udim
    woffset = udim + k + 2
    e1, f1 = 1 << woffset, 1 << (woffset + 1)
    Hgens = [1 << (woffset + 2 * i) for i in range(1, s - 1)]
    tags = [f1 ^ sum(g for j, g in enumerate(Hgens) if (t >> j) & 1)
            for t in range(1 << (s - 2))]
    zeta = [((a | (1 << k) | (quadratic(a, k) << (k + 1))) << toffset)
            for a in range(b)]
    z = [v ^ e1 for v in zeta]
    assert len(set(z)) == b
    edges = list(cube_edges(k))
    assert all(B(z[a], z[c]) == 1 for a, c in edges)
    assert all(B(zeta[a], zeta[c]) == quadratic(a ^ c, k)
               for a in range(b) for c in range(b))
    assert all(B(t, t2) == 0 for t in tags for t2 in tags)
    assert all(B(e1, t) == 1 for t in tags)

    # x(u) is the unique even-parity outer vertex with first r-1 bits u.
    # y(u) is the corresponding odd-parity outer vertex.
    F = [tuple(u ^ v for v in z) for u in range(m)]
    used = {v for f in F for v in f}
    assert len(used) == m * b
    assert all(B(f[a], f[c]) == 1 for f in F for a, c in edges)
    T = {t << toffset for t in range(1 << (k + 2 * s))}
    assert len(T) == D * b
    assert T & used == set(z)
    R = T - used
    assert len(R) == (D - 1) * b < m * b
    lists = [{v for v in R if B(v, z[a])} for a in range(b)]
    assert all(len(L) >= (D // 2 - 1) * b for L in lists)
    assert len({len(L) for L in lists}) == 1

    # Check every affine-basis constraint system.  The U-projection of
    # every endpoint is forced to zero, independent of its T-projection.
    for u in range(m):
        neighbors = [u] + [u ^ (1 << i) for i in range(udim)]
        assert len(set(neighbors)) == r
        assert binary_rank([v ^ neighbors[0] for v in neighbors[1:]]) == udim
    assert [v for v in range(1 << udim)
            if all(B(v, 1 << i) == 0 for i in range(udim))] == [0]

    # ALL 2^b distinct tag blocks (65,536 of them), not just a count formula.
    qtag = len(tags)
    candidate_count = qtag ** b
    assert candidate_count >= m
    candidate_set = set()
    chosen = []
    for code in range(candidate_count):
        t = code
        g = []
        for a in range(b):
            g.append(zeta[a] ^ tags[t % qtag])
            t //= qtag
        g = tuple(g)
        assert len(set(g)) == b
        assert not (set(g) & used)
        assert all(g[a] in lists[a] for a in range(b))
        assert all(B(g[a], g[c]) == 1 for a, c in edges)
        candidate_set.add(g)
        if code < m:
            chosen.append(g)
    assert len(candidate_set) == candidate_count
    assert len(set(F) | set(chosen)) == 2 * m

    # Actual outer Q_r: y(u) neighbors x(u) and x(u xor e_i).
    # Check every matching-coordinate original edge, and the disjointness
    # of the adjacent block images.  Nonadjacent odd blocks DO collide.
    checked = 0
    for u, g in enumerate(chosen):
        for v in [u] + [u ^ (1 << i) for i in range(udim)]:
            assert not (set(g) & set(F[v]))
            assert all(B(F[v][a], g[a]) == 1 for a in range(b))
            checked += b
    loads = Counter(v for g in chosen for v in g)
    assert max(loads.values()) > 1
    assert len(loads) < m * b
    assert m * b > len(R)

    # Two distinct, disjoint DRC roots common to ALL even blocks.
    roots = [tuple(v ^ tag for v in zeta) for tag in tags[:2]]
    assert not (set(roots[0]) & set(roots[1]))
    for a in range(b):
        assert sum(B(v, roots[0][a]) and B(v, roots[1][a]) for v in T) == len(T) // 4
    for root in roots:
        assert all(not (set(root) & set(f)) and
                   all(B(root[a], f[a]) for a in range(b)) for f in F)

    # Explicit original Q_d elsewhere in the SAME host: lift an odd
    # dimension into a base of even dimension d+1 and use one extra pair.
    base_dim = d + 1
    assert base_dim + 2 <= n
    def full_cube_lift(a):
        return a | (1 << base_dim) | (quadratic(a, base_dim) << (base_dim + 1))
    full_copy = [full_cube_lift(a) for a in range(1 << d)]
    assert len(set(full_copy)) == 1 << d
    assert all(B(full_copy[a], full_copy[c]) == 1 for a, c in cube_edges(d))

    print(f"PASS: k={k}, s={s}, N={N:,}, C={N // (1 << d)}; "
          f"{m:,} pairwise-disjoint even Q_{k} blocks.")
    print(f"PASS: {candidate_count:,} distinct residual common-neighbor blocks; "
          f"each of {m:,} opposite vertices has this same subfamily.")
    print(f"PASS: actual injective auxiliary Q_{r}; {checked:,} outer "
          "matching-coordinate edges checked; two disjoint DRC roots checked.")
    print(f"PASS: all residual candidates lie in {len(R):,} original vertices "
          f"for {m*b:,} required slots (Hall deficit {m*b-len(R):,}).")
    print(f"AUDIT: chosen odd blocks use only {len(loads)} original vertices; "
          f"maximum multiplicity {max(loads.values()):,}; row-list size {len(lists[0])}.")
    print(f"PASS: same host explicitly contains an ORIGINAL injective Q_{d}; "
          "this example is not a Ramsey counterexample.")


def audit_min_sum_gap():
    # A small exact product-of-linear-forms audit of the Jensen/min--sum
    # algebra, separate from the large symplectic construction.  Four
    # cyclic sectors; each has three rows supported on two columns.
    N, rows = 4, 3
    sectors = [((i, (i + 1) % N),) * rows for i in range(N)]
    outcomes = [(i, choices) for i, L in enumerate(sectors)
                for choices in product(*L)]
    assert len(outcomes) == 32
    assert all(len(set(choices)) < rows for _, choices in outcomes)
    total_loads = Counter(v for _, choices in outcomes for v in choices)
    assert all(Fraction(total_loads[v], len(outcomes)) == Fraction(3, 4)
               for v in range(N))
    # w_v = exp(-lambda_v).  Shared capped partition is P(w)/prod w.
    tested = 0
    for w in product([Fraction(1), Fraction(1, 2), Fraction(1, 4)], repeat=N):
        P = sum(prod(w[v] for v in choices) for _, choices in outcomes)
        assert P / prod(w) >= len(outcomes)
        if any(x < 1 for x in w):
            assert P / prod(w) > len(outcomes)
        tested += 1
    # Sector-adaptive penalty supported on its two columns has value
    # 8*t^(3-2)=8*t -> 0.  This is an exact identity, not an optimizer scan.
    for i in range(N):
        S = set(sectors[i][0])
        for t in [Fraction(1, 2), Fraction(1, 4), Fraction(1, 16)]:
            w = [t if v in S else Fraction(1) for v in range(N)]
            P = sum(prod(w[v] for v in choices)
                    for choices in product(*sectors[i]))
            assert P / prod(w) == 8 * t
    print(f"PASS: exact min--sum/stable-row toy audit: {tested} simultaneous "
          "penalty vectors; common minimum at zero but every sector cap is zero.")


def audit_parameters():
    checked, admissible = 0, 0
    max_gap = Fraction(0)
    for s in (3, 7, 11):
        D = 1 << (2 * s)
        for k in range(4, 514, 2):
            b, r, d = 1 << k, 3 * k + 1, 4 * k + 1
            N = D * b**4
            assert N >= 2 * (k + 1)
            assert Fraction(N - 1, 2 * N) >= Fraction(15, 32)
            assert 64 * (N - 1) > 2 * N
            # Exact exponent upper bounds for M and q_A in (2.30).
            assert Fraction(2, k*D*b) < Fraction(1, 2)
            assert (4 + Fraction(16, k+1) + Fraction(2*k, b*b)) / (D*b) < Fraction(1, 2)
            # (1-eps_k)(1-eps_(k+1))^r times finite-density correction.
            x = b * (7 * k // 2 + 1)
            error_bound = Fraction(1 + 8 * r, D * b) + Fraction(x, N)
            assert error_bound < Fraction(1, 2)
            # log_2 of the proved M q_A^r lower bound, no exponential in b
            # need be materialized.  It implies the ordinary DRC threshold.
            log2_lower = b * (k // 2 + 2 * s - 1) - 1
            assert log2_lower >= r + 2
            # Proves M q_A^r >= h^2 exp(kb/10), using 1/2 <= log 2 <= 1.
            assert b * (3 * k + 20 * s - 10) > 20 * (8 * k + 3)
            assert (s - 2) * b >= 3 * k
            if 3 * k >= 2 * s:
                assert b**3 > D - 1
                assert b**4 < N - 1  # unconditioned opposite load <1
                assert 2 * b**4 < N - 1  # even full-cube load <1
                admissible += 1
            # log(1+x)<=x and -log(1-1/N)<=2/N give this rational gap bound.
            gap = Fraction(1, (k + 1) * (1 << (2 * k + 2 * s - 4))) \
                  + Fraction(2 * (k + 1), N)
            if s == 7 and k >= 6:
                max_gap = max(max_gap, gap)
            checked += 1
    print(f"PASS: {checked} exact scale audits; {admissible} also have the "
          "capacity obstruction; all have majority density, flux, injective "
          "surplus, and the ordinary DRC threshold.")
    print(f"AUDIT: for C=8192 and even k>=6 in the audited range, "
          f"(k+1)Delta upper bound <= {float(max_gap):.12g}.")


def main():
    spec = Path(__file__).with_name("Spec.lean")
    expected = "9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b"
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == expected
    audit_small_symmetry()
    audit_root_counting_lemma()
    audit_concrete_auxiliary()
    audit_min_sum_gap()
    audit_parameters()
    print("Spec.lean SHA-256:", expected)
    print("All checks pass. No conflict-free DRC theorem or Ramsey proof is certified.")


if __name__ == "__main__":
    main()
