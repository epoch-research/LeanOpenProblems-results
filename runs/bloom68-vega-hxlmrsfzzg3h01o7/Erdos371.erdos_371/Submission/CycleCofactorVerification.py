#!/usr/bin/env python3
"""Exact finite checks for CycleCofactorResearch.md.

No Lean files are read. Computations check finite algebra, not a density theorem
or the analytic prime-producing theorem used in the infinite construction.
"""
from collections import Counter
from itertools import combinations
from math import gcd, isqrt, lcm, log, log1p, prod


def largest_prime_sieve(limit):
    p = [0] * (limit + 1)
    p[1] = 1
    for q in range(2, limit + 1):
        if p[q] == 0:
            for m in range(q, limit + 1, q):
                p[m] = q
    return p


def factor(m):
    ans = Counter()
    q = 2
    while q * q <= m:
        while m % q == 0:
            ans[q] += 1
            m //= q
        q = 3 if q == 2 else q + 2
    if m > 1:
        ans[m] += 1
    return ans


def signed_add(a, b, sign=1):
    # Counter subtraction discards negative coordinates; do NOT use it here.
    for p, e in b.items():
        a[p] += sign * e
        if a[p] == 0:
            del a[p]


def order(a, b):
    return (b > a) - (b < a)


def decompose(word, first_edge):
    """Partition all genuine edges into simple directed cycles and a path."""
    vertices = [word[0]]
    position = {word[0]: 0}
    edges = []
    cycles = []
    for n, w in enumerate(word[1:], first_edge):
        if w not in position:
            edges.append(n)
            position[w] = len(vertices)
            vertices.append(w)
        else:
            k = position[w]
            cycles.append(edges[k:] + [n])
            for old in vertices[k + 1:]:
                del position[old]
            vertices = vertices[:k + 1]
            edges = edges[:k]
    return cycles, edges


def v2(n):
    return (n & -n).bit_length() - 1


def cofactor_forms(slopes):
    """A, B linear polynomials for the shifted descending cycle."""
    A, B = [], []
    for a, b in zip(slopes, slopes[1:]):
        d = b - a
        assert gcd(a, b) == d
        v, u = a // d, b // d
        assert u == v + 1 and v % 2 == 0 and u % 2 == 1
        A.append((a, 1 + v))
        B.append((b, 1 + u))
    d = slopes[-1] - slopes[0]
    v, u = slopes[0] // d, slopes[-1] // d
    A.append((slopes[-1], 1 - u))
    B.append((slopes[0], 1 - v))
    return A, B


def value(f, t):
    return f[0] * t + f[1]


def main():
    limit = 600000
    P = largest_prime_sieve(limit + 1)
    Q = [0] + [n // P[n] for n in range(1, limit + 2)]

    # All cofactor prime labels are at most the square root of the integer.
    for n in range(2, limit + 2):
        assert P[Q[n]] ** 2 <= n
        if n >= 3 and n <= limit:
            assert order(P[n], P[n + 1]) == -order(Q[n], Q[n + 1])
    print(f"PASS: {limit - 2} cofactor order reversals; {limit} square-root support checks")

    cycle_count = 0
    edge_count = 0
    sample_counts = []
    for N in list(range(2, 301)) + [500, 1000, 5000, 10000, 50000]:
        assert P[N] == P[2 * N]
        cycles, path = decompose(P[N:2 * N + 1], N)
        assert not path
        assert sorted(n for c in cycles for n in c) == list(range(N, 2 * N))
        total_defect = Counter()
        total_delta = 0.0
        cycle_bias = 0
        for cycle in cycles:
            r = len(cycle)
            labels = [P[n] for n in cycle]
            assert len(set(labels)) == r
            assert all(P[n + 1] == labels[(i + 1) % r]
                       for i, n in enumerate(cycle))
            A = prod(Q[n] for n in cycle)
            B = prod(Q[n + 1] for n in cycle)
            assert B > A
            assert B * prod(cycle) == A * prod(n + 1 for n in cycle)
            g = gcd(A, B)
            defect = Counter()
            for n in cycle:
                signed_add(defect, factor(Q[n + 1]))
                signed_add(defect, factor(Q[n]), -1)
            assert all(p * p <= 2 * N for p in defect)
            assert prod(p ** e for p, e in defect.items() if e > 0) == B // g
            assert prod(p ** -e for p, e in defect.items() if e < 0) == A // g
            norm = sum(abs(e) * log(p) for p, e in defect.items())
            delta = sum(log1p(1 / n) for n in cycle)
            assert abs(norm - log(A // g) - log(B // g)) < 1e-8
            assert norm + 1e-8 >= 2 * log(N / (2 * r))
            assert 0 < delta <= r / N + 1e-12
            signed_add(total_defect, defect)
            total_delta += delta
            cycle_bias += sum(order(P[n], P[n + 1]) for n in cycle)
        assert dict(total_defect) == {2: 1}
        assert abs(total_delta - log(2)) < 1e-9
        assert cycle_bias == sum(order(P[n], P[n + 1]) for n in range(N, 2 * N))
        cycle_count += len(cycles)
        edge_count += N
        if N >= 5000:
            sample_counts.append((N, len(cycles), max(map(len, cycles)), cycle_bias))
    print(f"PASS: {cycle_count} simple dyadic cycles, {edge_count} edge checks; total defect exactly e_2")
    print("Dyadic samples (N, number of cycles, longest cycle, signed current):", sample_counts)

    # The prefix path can be discarded in counting norm and also has small
    # cofactor logarithmic mass. Check the finite inequality used in the proof.
    for X in [10, 100, 1000, 10000, 100000]:
        cycles, path = decompose(P[1:X + 2], 1)
        assert sorted([n for c in cycles for n in c] + path) == list(range(1, X + 1))
        pi = sum(P[p] == p for p in range(2, X + 2))
        assert len(path) <= pi
        path_log = sum(log(Q[n]) + log(Q[n + 1]) for n in path)
        bound = 2 * sum(log((X + 1) / p) for p in range(2, X + 2) if P[p] == p)
        assert path_log <= bound + 1e-8
        D = Counter()
        for c in cycles:
            for n in c:
                signed_add(D, factor(Q[n + 1]))
                signed_add(D, factor(Q[n]), -1)
        rhs = factor(Q[X + 1])
        for n in path:
            signed_add(rhs, factor(Q[n + 1]), -1)
            signed_add(rhs, factor(Q[n]))
        assert D == rhs
    print("PASS: five full-prefix decompositions and their logarithmic boundary bound")

    # Real lower-cofactor cycle with zero full valuation defect and nonzero skew.
    assert Q[7:12] == [1, 4, 3, 2, 1]
    assert sum(order(Q[n], Q[n + 1]) for n in range(7, 11)) == -2
    assert prod(Q[n] for n in range(7, 11)) == prod(Q[n + 1] for n in range(7, 11)) == 24
    for N, expected in [(3, -1), (5, 1)]:
        assert sum(order(P[n], P[n + 1]) for n in range(N, 2 * N)) == expected
        assert prod(Q[n + 1] for n in range(N, 2 * N)) == 2 * prod(Q[n] for n in range(N, 2 * N))
    cycle_minus = [5, 12, 13, 14]
    cycle_zero = [10, 11, 6, 14]
    for cycle, expected in [(cycle_minus, -2), (cycle_zero, 0)]:
        labels = [P[n] for n in cycle]
        assert len(set(labels)) == 4
        assert all(P[n + 1] == labels[(i + 1) % 4] for i, n in enumerate(cycle))
        assert prod(Q[n] for n in cycle) == 8
        assert prod(Q[n + 1] for n in cycle) == 12
        assert sum(order(P[n], P[n + 1]) for n in cycle) == expected
    weights = Counter()
    for cycle, coefficient in [(cycle_minus, 1), (cycle_zero, -1)]:
        for n in cycle:
            weights[n] += coefficient
    boundary, source_factors, target_factors = Counter(), Counter(), Counter()
    for n, c in weights.items():
        signed_add(boundary, {P[n + 1]: c, P[n]: -c})
        signed_add(source_factors, factor(Q[n]), c)
        signed_add(target_factors, factor(Q[n + 1]), c)
    assert not boundary and not source_factors and not target_factors
    assert sum(weights.values()) == 0
    assert sum(c * order(P[n], P[n + 1]) for n, c in weights.items()) == -2
    print("PASS: zero-defect cofactor cycle; opposite-bias dyadic walks; equal-inventory simple cycles")

    # A small all-high-prime directed triangle, independent of the infinite family.
    ns = [33, 51, 65]
    assert [P[n] for n in ns] == [11, 17, 13]
    assert [P[n + 1] for n in ns] == [17, 13, 11]
    assert min(P[n] for n in ns) ** 2 > max(n + 1 for n in ns)
    assert prod(Q[n] for n in ns) == 45 and prod(Q[n + 1] for n in ns) == 48
    print("PASS: 11 -> 17 -> 13 -> 11 is a genuine directed high-prime triangle")

    # Finite certificate for the shifted cycle. Simultaneous primality of this
    # PARTICULAR triple infinitely often is NOT used in the proof.
    slopes = [12, 14, 15]
    t = 50
    ps = [a * t + 1 for a in slopes]
    assert ps == [601, 701, 751] and all(P[p] == p for p in ps)
    ns = [ps[2] * (ps[1] + 14), ps[1] * (ps[0] + 6), ps[0] * (ps[2] - 5)]
    assert ns == [536965, 425507, 448346]
    assert [P[n] for n in ns] == [751, 701, 601]
    assert [P[n + 1] for n in ns] == [701, 601, 751]
    assert sum(order(P[n], P[n + 1]) for n in ns) == -1
    A = prod(Q[n] for n in ns)
    B = prod(Q[n + 1] for n in ns)
    assert (A, B, gcd(A, B), B - A) == (323767730, 323769816, 2, 2086)
    AA, BB = cofactor_forms(slopes)
    R = prod(abs(a * d - b * c) for a, b in AA for c, d in BB)
    assert R > 0
    for t in range(1, 1001):
        a = prod(value(f, t) for f in AA)
        b = prod(value(f, t) for f in BB)
        assert b - a == 41 * t + 36
        assert R % gcd(a, b) == 0
    print("PASS: narrow-scale numerical cycle and 1000 resultant/gcd checks")
    print("Numerical cycle cofactors:", [(n, Q[n], Q[n + 1]) for n in ns])

    # Recursively produce admissible slope sets, including the final large
    # translation used to exclude common roots of cofactor polynomials.
    S = [1]
    subset_count = 0
    for k in range(2, 7):
        D = max(S)
        L = lcm(*(S + [b - a for a, b in combinations(S, 2)]))
        L *= 2 ** max(0, 1 + max(map(v2, S)) - v2(L))
        threshold = max(2 * D * D + 1, 100 * D)
        M = L * ((threshold + L - 1) // L)
        S = [M] + [M + s for s in S]
        assert all(gcd(a, b) == b - a for a, b in combinations(S, 2))
        assert all(v2(a) > v2(b) for a, b in zip(S, S[1:]))
        assert all(a + c != 2 * b for a, b, c in combinations(S, 3))
        for r in range(3, k + 1):
            for I in combinations(S, r):
                A, B = cofactor_forms(I)
                assert all(a * d - b * c != 0 for a, b in A for c, d in B)
                for t in [2, 5, 11]:
                    ps = [a * t + 1 for a in I]
                    # Pure polynomial/Diophantine checks: ps need not be prime.
                    ns = []
                    for a, b, p, q in zip(I, I[1:], ps, ps[1:]):
                        d = b - a
                        v, u = a // d, b // d
                        assert u * p - v * q == 1
                        n = (p + v) * q
                        assert n + 1 == (q + u) * p
                        ns.append(n)
                    d = I[-1] - I[0]
                    u, v = I[-1] // d, I[0] // d
                    n = (ps[-1] - u) * ps[0]
                    assert n + 1 == (ps[0] - v) * ps[-1]
                    ns.append(n)
                    aa = prod(value(f, t) for f in A)
                    bb = prod(value(f, t) for f in B)
                    assert bb > aa
                    assert bb * prod(ns) == aa * prod(n + 1 for n in ns)
                subset_count += 1
    print(f"PASS: slope recursion through k=6; {subset_count} subset-cycle polynomial systems")
    print("All finite checks passed. No asymptotic density or simultaneous-primality conjecture tested.")


if __name__ == '__main__':
    main()
