#!/usr/bin/env python3
"""Exact audits for CubeGlobalReflectionCompletion.md.

No Ramsey conclusion is asserted. Actual host injections are used in the
small brute-force checks; other tests audit proved all-dimensional formulas.
Only the Python standard library is used.
"""
from collections import Counter
from fractions import Fraction
from itertools import permutations
from math import comb, factorial, log
from pathlib import Path
import hashlib


SPEC_HASH = "9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b"
ROOT = Path(__file__).resolve().parent


def cube_edges(d):
    return [(x, x ^ (1 << i)) for x in range(1 << d)
            for i in range(d) if not (x & (1 << i))]


def falls(n, h):
    out = [1]
    for s in range(h):
        out.append(out[-1] * (n - s))
    return out


def phase_pattern(phase, edges):
    return sum(1 << j for j, (x, y) in enumerate(edges)
               if ((phase >> x) ^ (phase >> y)) & 1)


def cut_size(pattern, h, edges):
    adjacency = [[] for _ in range(h)]
    for j, (x, y) in enumerate(edges):
        c = (pattern >> j) & 1
        adjacency[x].append((y, c))
        adjacency[y].append((x, c))
    labels = [None] * h
    labels[0] = 0
    queue = [0]
    for x in queue:
        for y, c in adjacency[x]:
            want = labels[x] ^ c
            if labels[y] is None:
                labels[y] = want
                queue.append(y)
            elif labels[y] != want:
                return None
    assert len(queue) == h  # Connected source: the phase is unique up to flip.
    return sum(labels)


def reduced_pattern(d, distinguished, w, edges):
    out = 0
    for j, (x, y) in enumerate(edges):
        if x ^ y == 1 << distinguished:
            parity_other = (x & ~(1 << distinguished)).bit_count() & 1
            colour = w[parity_other]
        else:
            colour = w[2 + ((x >> distinguished) & 1)]
        out |= colour << j
    return out


def weighted_falls_dp(weights, h):
    # Product (1+w*z); s! times its z^s coefficient counts labelled injections.
    coeff = [Fraction(1)] + [Fraction(0)] * h
    for w in weights:
        for s in range(h, 0, -1):
            coeff[s] += w * coeff[s - 1]
    return [factorial(s) * coeff[s] for s in range(h + 1)]


def weighted_falls_recurrence(b, p, epsilon, h):
    # Derived independently from (1+z)^b(1+epsilon*z)^p.
    out = [Fraction(1), b + p * epsilon]
    for s in range(1, h):
        out.append((b + p * epsilon - s * (1 + epsilon)) * out[-1]
                   + epsilon * s * (b + p - s + 1) * out[-2])
    return out


def weighted_falls_sum(b, p, epsilon, h):
    # Choose which source labels use exceptional images, then inject both parts.
    B, P = falls(b, h), falls(p, h)
    powers = [epsilon ** j for j in range(h + 1)]
    return [sum((comb(s, j) * P[j] * powers[j] * B[s - j]
                 for j in range(min(s, p) + 1)), Fraction(0))
            for s in range(h + 1)]


def audit_actual_injections():
    cases = [(2, 4, 4, 0, Fraction(1)),
             (2, 5, 4, 1, Fraction(1, 5)),
             (2, 6, 4, 2, Fraction(1, 10)),
             (3, 4, 4, 0, Fraction(1)),
             (3, 5, 3, 2, Fraction(1)),
             (3, 5, 3, 2, Fraction(1, 3))]
    total = 0
    for d, a, b, p, epsilon in cases:
        h, n = 1 << d, a + b
        edges = cube_edges(d)
        # The last p vertices in A are exceptional. All original labels remain.
        weights = [epsilon if a - p <= v < a else Fraction(1)
                   for v in range(n)]
        ZA = weighted_falls_dp(weights[:a], h)
        ZB = weighted_falls_dp(weights[a:], h)
        actual = Counter()
        powers = [epsilon ** k for k in range(h + 1)]
        for phi in permutations(range(n), h):
            assert len(set(phi)) == h
            phase = sum(1 << x for x in range(h) if phi[x] < a)
            pattern = phase_pattern(phase, edges)
            exceptional_used = sum(a - p <= v < a for v in phi)
            actual[pattern] += powers[exceptional_used]
            total += 1
        expected = {}
        # Choose the representative phase with source vertex 0 outside A.
        for phase in range(0, 1 << h, 2):
            s = phase.bit_count()
            pattern = phase_pattern(phase, edges)
            assert pattern not in expected
            expected[pattern] = ZA[s] * ZB[h - s] + ZA[h - s] * ZB[s]
        assert len(expected) == 1 << (h - 1)
        assert dict(actual) == {k: v for k, v in expected.items() if v}
        assert sum(actual.values()) == weighted_falls_dp(weights, h)[h]
    print(f"Actual full injections: {total:,} in {len(cases)} host/weight cases PASS")


def audit_reduced_classification():
    tested = 0
    sizes_by_d = {}
    for d in range(2, 9):
        h, edges = 1 << d, cube_edges(d)
        sizes = set()
        consistent = inconsistent = 0
        for distinguished in range(d):
            for bits in range(16):
                w = tuple((bits >> j) & 1 for j in range(4))
                pattern = reduced_pattern(d, distinguished, w, edges)
                s = cut_size(pattern, h, edges)
                if s is None:
                    inconsistent += 1
                    assert sum(w) & 1
                else:
                    consistent += 1
                    assert not (sum(w) & 1)
                    assert s % (h // 4) == 0
                    sizes.add(s)
                tested += 1
        assert consistent == inconsistent == 8 * d
        assert {min(s, h - s) for s in sizes} == {0, h // 4, h // 2}
        sizes_by_d[d] = sizes
    print(f"Reduced square-pattern cut classification: {tested} representations PASS")
    return sizes_by_d


def audit_exponential_transfer(sizes_by_d):
    tested = 0
    example = None
    for C in (3, 4, 16, 64, 4096):
        for d in range(3, 11):
            t, h = 1 << (d - 3), 1 << d
            a, b = (4 * C + 1) * t, (4 * C - 1) * t
            assert a + b == C * h and b >= h
            A, B = falls(a, h), falls(b, h)
            f = [A[s] * B[h - s] for s in range(h + 1)]
            T = [f[s] + f[h - s] for s in range(h + 1)]
            M, MR = max(T), max(T[2 * j * t] for j in range(5))
            assert MR == T[4 * t] == 2 * f[4 * t]
            assert 0 < T[0] <= T[4 * t]
            assert f[6 * t] == f[4 * t] and f[8 * t] == f[2 * t]
            assert f.index(max(f)) == 5 * t
            assert M >= T[5 * t] >= f[5 * t]
            numerator, denominator = (4 * C - 4) ** t, (4 * C - 3) ** t
            assert MR * denominator <= 2 * M * numerator
            assert (T[0] + T[4 * t]) * denominator <= 4 * M * numerator
            if d in sizes_by_d:
                assert max(T[s] for s in sizes_by_d[d]) == MR
            if C == 3 and d == 10:
                example = log(M) - log(MR)
            tested += 1
    print(f"Full maximum, reduced maximum, two-colour ratio: {tested} exact cases PASS")
    print(f"Example C=3, d=10: log(M/M_R)={example:.6f} (display only; checks exact)")


def audit_sparse_repair():
    tested = 0
    for h in range(2, 25, 2):
        for b in (h, h + 1, 2 * h, 20 * h):
            for p in (1, h // 2, 3 * h):
                epsilon = Fraction(b - h + 1, p * (b + 1))
                assert 0 < epsilon < 1
                ZA = weighted_falls_recurrence(b, p, epsilon, h)
                assert ZA == weighted_falls_sum(b, p, epsilon, h)
                if b + p <= 40:
                    assert ZA == weighted_falls_dp([Fraction(1)] * b
                                                   + [epsilon] * p, h)
                B = falls(b, h)
                g = [ZA[s] * B[h - s] for s in range(h + 1)]
                for s in range(h):
                    ratio = ZA[s + 1] / ZA[s]
                    assert b - s <= ratio < b - s + 1
                    # Recover E K from the exact appending identity (9).
                    mean_K = (ratio - (b - s + p * epsilon)) / (1 - epsilon)
                    assert 0 <= mean_K <= Fraction(s * p, b - s + 1) * epsilon
                    assert (g[s + 1] > g[s]) == (s < h // 2)
                T = [g[s] + g[h - s] for s in range(h + 1)]
                assert g.index(max(g)) == h // 2
                assert max(T) == T[h // 2] >= 2 * B[h // 2] ** 2 > 0
                tested += 1
    print(f"Sparse positive-weight ratio and global pattern maximum: {tested} cases PASS")
    tested_family = 0
    for C in (3, 16, 64, 4096):
        for d in range(3, 9):
            t, h = 1 << (d - 3), 1 << d
            b, p = (4 * C - 1) * t, 2 * t
            epsilon = Fraction(b - h + 1, p * (b + 1))
            ZA = weighted_falls_recurrence(b, p, epsilon, h)
            B = falls(b, h)
            g = [ZA[s] * B[h - s] for s in range(h + 1)]
            T = [g[s] + g[h - s] for s in range(h + 1)]
            assert max(T) == max(T[2 * j * t] for j in range(5)) == T[h // 2]
            assert 4 * C * p == C * h
            if C >= 32:
                assert 128 * p <= C * h
            tested_family += 1
    print(f"Explicit counterexample family repaired, including sparse budget: {tested_family} cases PASS")


def main():
    before = hashlib.sha256((ROOT / "Spec.lean").read_bytes()).hexdigest()
    assert before == SPEC_HASH
    audit_actual_injections()
    sizes_by_d = audit_reduced_classification()
    audit_exponential_transfer(sizes_by_d)
    audit_sparse_repair()
    after = hashlib.sha256((ROOT / "Spec.lean").read_bytes()).hexdigest()
    assert after == before
    print(f"Spec.lean unchanged: SHA-256 {after}")
    print("Full conjecture proved: NO. Universal weighted/zero-level inequality remains unproved.")


if __name__ == "__main__":
    main()
