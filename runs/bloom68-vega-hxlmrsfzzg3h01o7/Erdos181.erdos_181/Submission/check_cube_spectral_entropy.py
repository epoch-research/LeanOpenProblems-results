#!/usr/bin/env python3
"""Finite checks for CubeSpectralEntropyProgress.md.

The general statements are proved in the Markdown file.  This script checks
small exhaustive instances, exact occupancy identities, and explicit constants;
it does NOT test or assert the unresolved constant-multiplier embedding theorem.
"""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import comb, exp, floor, isqrt, log, prod, sqrt
from pathlib import Path
import hashlib

import numpy as np


SPEC_HASH = "9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b"


def cube_edges(d):
    return [(v, v ^ (1 << i)) for v in range(1 << d)
            for i in range(d) if v < (v ^ (1 << i))]


def falling(n, k):
    return prod(range(n - k + 1, n + 1)) if 0 <= k <= n else 0


def random_host(n, seed):
    rng = np.random.default_rng(seed)
    upper = np.triu((rng.random((n, n)) < 0.5).astype(np.int64), 1)
    return upper + upper.T


def symplectic_host(r, omit_zero=False):
    # The first r bits are e coordinates and the last r bits f coordinates.
    labels = list(range(1 if omit_zero else 0, 1 << (2 * r)))
    low = (1 << r) - 1
    def pairing(x, y):
        return (((x & low) & (y >> r)).bit_count()
                + ((x >> r) & (y & low)).bit_count()) % 2
    A = np.array([[int(x != y and pairing(x, y) == 0)
                   for y in labels] for x in labels], dtype=np.int64)
    return A


def check_constants():
    fail = exp(-0.5) + 2 * exp(-2 * (4 - log(9)))
    assert fail < 0.661
    margin = 0.25 + 1 / 30 - 0.5 * log(16)
    assert margin < -1
    assert 4 / exp(1) + log(2) < 3
    print(f"Density-preserving thinning: simultaneous failure bound {fail:.12f} < 1")
    print(f"Suppression exponent: 1/4 + 1/30 - (log 16)/2 = {margin:.12f} < -1")

    # Exact finite-population inequalities, including the loop-density correction.
    for n in range(2, 90):
        for h in range(2, n + 1):
            f = falling(n, h)
            e_max = h * (h - 1) // 2
            assert Fraction(f, n ** h) <= Fraction(n - 1, n) ** e_max
            log_ratio = sum(-log(1 - i / n) for i in range(h))
            assert log_ratio <= h * (h - 1) / (2 * (n - h + 1)) + 1e-10
    for n in range(1, 40):
        for a in range(n + 1):
            assert sum(comb(n, j) for j in range(a + 1)) <= (n + 1) ** a
    print("Finite-population baseline and small-set encoding inequalities: exact checks passed")


def check_containers():
    """Exhaust all support systems for a three-type path on an 8-vertex host."""
    n = 8
    A = random_host(n, 742 + n)
    op = float(np.max(np.abs(np.linalg.eigvalsh(A - 0.5 * np.ones((n, n))))))
    # A harmless upward perturbation makes norm-based comparisons one-sided.
    op_bound = op + 1e-9
    masks = range(1, 1 << n)
    verts = {s: [v for v in range(n) if s & (1 << v)] for s in masks}
    sizes = {s: s.bit_count() for s in masks}
    neighbor = [sum(int(A[x, y]) << y for y in range(n)) for x in range(n)]
    H = cube_edges(2)
    tau = [0, 1, 1, 2]
    matching = [(0, 1), (2, 3)]
    total = big_total = exception_total = 0
    for rho in (Fraction(1), Fraction(3, 4)):
        delta = float(rho - Fraction(1, 2))
        beta2n = (op_bound / delta) ** 2
        beta2 = beta2n / n
        a = min(n, floor(op_bound / delta))
        R = max(1.0, n / beta2)
        den, num = rho.denominator, rho.numerator
        def compat(s, t):
            return (all(den * (neighbor[x] & t).bit_count() >= num * sizes[t]
                        for x in verts[s])
                    and all(den * (neighbor[y] & s).bit_count() >= num * sizes[s]
                            for y in verts[t]))
        compatible = {s: [t for t in masks if compat(s, t)] for s in masks}
        seen = {}
        local = local_big = 0
        # The quotient edges are 0--1--2. Repeated support sets are permitted.
        for s1 in masks:
            for s0, s2 in product(compatible[s1], repeat=2):
                support = (s0, s1, s2)
                for exceptional in (frozenset(), frozenset({1})):
                    # Removing vertex 1 retains the same quotient path.
                    edges = [(u, v) for u, v in H
                             if u not in exceptional and v not in exceptional]
                    F = {(tau[u], tau[v]) for u, v in edges}
                    F |= {(j, i) for i, j in tuple(F)}
                    small = {i for i, s in enumerate(support) if sizes[s] <= a}
                    assert all(i in small or j in small for i, j in F)
                    fingerprint = tuple(support[i] if i in small else 0 for i in range(3))
                    canonical = list(support)
                    for i in set(range(3)) - small:
                        T = (1 << n) - 1
                        for j in range(3):
                            if (i, j) in F:
                                assert j in small
                                high = sum(1 << x for x in range(n)
                                           if den * (neighbor[x] & support[j]).bit_count()
                                           >= num * sizes[support[j]])
                                T &= high
                        canonical[i] = T
                        assert support[i] & ~T == 0
                    key = (exceptional, fingerprint)
                    if key in seen:
                        assert seen[key] == tuple(canonical)
                    else:
                        seen[key] = tuple(canonical)
                    for i, j in F:
                        assert canonical[i].bit_count() * canonical[j].bit_count() <= beta2n + 1e-6
                    domains = [n if v in exceptional else canonical[tau[v]].bit_count()
                               for v in range(4)]
                    box = prod(domains)
                    hit = sum(u in exceptional or v in exceptional for u, v in matching)
                    exact_match_bound = beta2n ** (2 - hit) * n ** (2 * hit)
                    assert box <= exact_match_bound + 1e-5
                    assert box <= beta2n ** 2 * R ** len(exceptional) + 1e-5
                    U = [v for v in range(4) if v not in exceptional and tau[v] in small]
                    assert len(U) >= 2 - len(exceptional)
                    union = 0
                    for i in small:
                        union |= support[i]
                    assert union.bit_count() <= 3 * a
                    local += 1
                    local_big += len(small) < 3
                    exception_total += bool(exceptional)
        D = sum(comb(n, j) for j in range(1, a + 1))
        assert len(seen) <= 2 * (1 + D) ** 3
        total += local
        big_total += local_big
        print(f"Exhaustive containers: rho={rho}, a={a}, systems={local}, big-pool systems={local_big}, fingerprints={len(seen)}")
    assert total > 0 and big_total > 0 and exception_total > 0

    # A genuinely non-complete dense phase. Its canonical enlargement is NOT
    # asserted to preserve both directional minimum-degree conditions.
    A = symplectic_host(4)
    n = len(A)
    E = A - 0.5 * np.ones((n, n))
    assert np.allclose(np.sort(np.abs(np.linalg.eigvalsh(E)))[-1], 9)
    S = [0, 1, 2, 4]
    Tstar = [x for x in range(n) if 4 * sum(A[x, y] for y in S) >= 3 * len(S)]
    Tbase = [x for x in Tstar if x not in S]
    # Remove four points from each of the three one-nonneighbour patterns.
    remove = set()
    for u in S[1:]:
        pattern = [x for x in Tbase if A[u, x] == 0
                   and sum(A[v, x] for v in S[1:]) == 2]
        assert len(pattern) == 32
        remove.update(pattern[:4])
    assert len(remove) == 12
    T = [x for x in Tbase if x not in remove]
    assert len(Tstar) == 128 and len(T) == 112
    assert all(4 * sum(A[x, y] for y in T) >= 3 * len(T) for x in S)
    assert all(4 * sum(A[x, y] for y in S) >= 3 * len(S) for x in T)
    assert any(A[x, y] == 0 for x in S for y in T)
    assert len(T) > 36 == floor(9 / 0.25)
    assert any(4 * sum(A[x, y] for y in Tstar) < 3 * len(Tstar) for x in S)
    assert sum(A[x, y] for x in S for y in Tstar) >= 0.75 * len(S) * len(Tstar)
    print("Non-complete 3/4-dense phase: |S|=4, |T|=112, enlarged |T*|=128; only the claimed average-density property survives")


def check_profile_bounds():
    A = symplectic_host(2, omit_zero=True)
    n0 = len(A)
    L = 3
    # Red clone graph: equal-label distinct clones are adjacent.
    Bgraph = np.kron(A + np.eye(n0, dtype=np.int64), np.ones((L, L), dtype=np.int64))
    np.fill_diagonal(Bgraph, 0)
    n = len(Bgraph)
    p = Fraction(int(Bgraph.sum()), n * (n - 1))
    centered = Bgraph - float(p) * (np.ones((n, n)) - np.eye(n))
    op = float(np.max(np.abs(np.linalg.eigvalsh(centered))))
    alpha = min(float(p), 1 - float(p))
    assert op ** 2 + 1e-8 >= alpha ** 2 * L * (n - L)
    # H_0^2 = M I - J, and H_0 has eigenvalues +/- sqrt(M) on 1^perp.
    M = n0 + 1
    H0 = 2 * (A + np.eye(n0)) - np.ones((n0, n0))
    assert np.array_equal(H0 @ H0, M * np.eye(n0) - np.ones((n0, n0)))
    assert op + 1e-8 >= L * sqrt(M) / 2 - 1
    print(f"Clone lower bound: M={M}, L={L}, N={n}, actual ||B||={op:.9f}, eigen lower bound={L*sqrt(M)/2-1:.9f}")

    # General approximate-profile estimate, including disagreements.
    A = random_host(10, 812)
    E = A - 0.5 * np.ones_like(A)
    op = float(np.max(np.abs(np.linalg.eigvalsh(E))))
    tested = 0
    for S in ([0], [0, 1], [0, 1, 2], [2, 4, 6]):
        T = [v for v in range(10) if v not in S]
        for pattern in ([0] * len(T), [1] * len(T), [int(A[S[0], v]) for v in T]):
            errors = sum(int(A[x, y]) != pattern[j] for x in S for j, y in enumerate(T))
            eps = errors / (len(S) * len(T))
            if eps < 0.5:
                assert (0.5 - eps) ** 2 * len(S) * len(T) <= op ** 2 + 1e-9
                tested += 1
    assert tested > 0
    print(f"Approximate repeated-profile inequality: {tested} non-vacuous tests passed")


def stirling_second(n):
    S = [[0] * (n + 1) for _ in range(n + 1)]
    S[0][0] = 1
    for k in range(1, n + 1):
        for j in range(1, k + 1):
            S[k][j] = S[k - 1][j - 1] + j * S[k - 1][j]
    return S


def check_exact_occupancy():
    # A complete product phase has an exact, positive collision-defect polynomial.
    for m, s, t in ((2, 3, 4), (4, 2, 7), (32, 1, 63), (64, 4, 28)):
        S = stirling_second(m)
        coeff = Counter()
        for i in range(1, min(s, m) + 1):
            for j in range(1, min(t, m) + 1):
                coeff[2 * m - i - j] += falling(s, i) * S[m][i] * falling(t, j) * S[m][j]
        assert sum(coeff.values()) == (s * t) ** m
        assert coeff[0] == falling(s, m) * falling(t, m)
        if min(s, t) < m:
            assert coeff[0] == 0
    print("Exact biclique occupation polynomials: total hom count and actual injective coefficient agree")

    # Signed partition-lattice sum, with the entire occupancy background retained.
    # The block-size recurrence computes sum_pi product_B (-1)^(|B|-1)(|B|-1)!.
    z = [1]
    for n in range(1, 16):
        val = sum(comb(n - 1, k - 1) * (-1) ** (k - 1) * falling(k - 1, k - 1) * z[n - k]
                  for k in range(1, n + 1))
        z.append(val)
        assert val == int(n == 1)
    for occupancy in ((1, 1, 1), (2, 1, 1), (3, 2), (4, 4), (8, 1)):
        assert prod(z[n] for n in occupancy) == int(all(n == 1 for n in occupancy))
    print("Full collision-Mobius background: exact cancellation checked through fibre size 15")

    # A small actual graph with a planted Q_3: enumerate homomorphisms, not just boxes.
    n, d = 10, 3
    A = random_host(n, 3251)
    edges = cube_edges(d)
    for u, v in edges:
        A[u, v] = A[v, u] = 1
    h = 1 << d
    previous = [[u for u in range(v) if (u ^ v).bit_count() == 1] for v in range(h)]
    X = [v for v in range(h) if v.bit_count() % 2 == 0]
    Y = [v for v in range(h) if v.bit_count() % 2 == 1]
    all_poly, star_poly, keep_poly = Counter(), Counter(), Counter()
    assignment = [-1] * h
    def visit(v):
        if v == h:
            defect = h - len(set(assignment))
            all_poly[defect] += 1
            star = len({assignment[x] for x in X}) == 1 or len({assignment[y] for y in Y}) == 1
            (star_poly if star else keep_poly)[defect] += 1
            return
        for image in range(n):
            if all(A[assignment[u], image] for u in previous[v]):
                assignment[v] = image
                visit(v + 1)
    visit(0)
    assert all_poly == star_poly + keep_poly
    assert all_poly[0] == keep_poly[0] > 0
    assert star_poly[0] == 0 and sum(star_poly.values()) > 0
    Z, Zkeep = sum(all_poly.values()), sum(keep_poly.values())
    I = all_poly[0]
    assert Fraction(I, Z) == Fraction(Zkeep, Z) * Fraction(I, Zkeep)
    print(f"Actual Q_3 counts in a 10-vertex host: hom={Z}, deleted star-phase hom={sum(star_poly.values())}, inj={I}; exact pruning identity passed")


def check_quantified_regimes():
    K, Lambda = 1, 7  # Lambda = K+6 from density-preserving thinning.
    beta = 2 * Lambda
    C = 16 * beta * beta
    # The reflection template has t=4m, with at most 4D_* exceptional positions.
    Dstar = 21
    rows = []
    for a_source in (24, 32, 40, 48, 56):
        d = 3 * a_source + 2
        h = 1 << d
        N = C * h
        m = 1 << a_source
        t, s = 4 * m, 4 * Dstar
        a = min(N, isqrt(beta * beta * N))
        # A conservative bound on log sum_{j<=s} binom(h,j) R^j.
        R = N / (beta * beta)
        log_B_upper = log(s + 1) + s * (log(h) + log(R))
        entropy_budget = t * a * log(N + 1) + log_B_upper
        reflection_forbidden = t * a + s < h / 4
        suppression = entropy_budget <= h / 4
        rows.append((d, entropy_budget / h, reflection_forbidden, suppression))
    assert rows[-1][-1] and rows[-1][-2]
    print(f"Explicit endpoint regimes: K={K}, Lambda={Lambda}, C={C}, t=4*2^((d-2)/3), s=84")
    for d, budget, empty, suppressed in rows:
        print(f"  d={d:3d}: budget/h <= {budget:.9g}; half-injective phase forbidden={empty}; exp(-h) suppression certified={suppressed}")

    # A simple sufficient threshold for fixed t, no exceptional vertices.
    for beta in (1, 2, 14):
        for t in (1, 2, 5):
            C = 16 * beta * beta * t * t
            lower_N = (16 * beta * t * C) ** 4
            assert 3 * beta * t * C / lower_N ** 0.25 <= 3 / 16 + 1e-12
    print("Fixed-t sufficient threshold N >= (16 beta t C)^4: verified with margin 3/16 < 1/4")


def main():
    spec = Path(__file__).with_name("Spec.lean")
    digest = hashlib.sha256(spec.read_bytes()).hexdigest()
    assert digest == SPEC_HASH
    check_constants()
    check_containers()
    check_profile_bounds()
    check_exact_occupancy()
    check_quantified_regimes()
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_HASH
    print("Spec.lean SHA-256 unchanged:", digest)
    print("PASS: finite checks support the proved phase-elimination theorem; no full embedding theorem is asserted.")


if __name__ == "__main__":
    main()
