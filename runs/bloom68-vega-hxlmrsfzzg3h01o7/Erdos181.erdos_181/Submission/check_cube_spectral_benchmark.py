#!/usr/bin/env python3
"""Checks for CubeSpectralBenchmark.md and CubeSignedActivityLemmas.md.

These tests check proved identities and actual certificates. They do not replace
any all-dimensional argument in the proof, and do not certify the unresolved
constant-multiplier spectral benchmark.
"""
from __future__ import annotations

import hashlib
import itertools as it
import json
import math
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import random

import numpy as np

ROOT = Path(__file__).resolve().parent
SPEC_SHA = "9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b"


def check_spec():
    got = hashlib.sha256((ROOT / "Spec.lean").read_bytes()).hexdigest()
    assert got == SPEC_SHA, got
    return got


def partitions(items):
    items = tuple(items)
    if not items:
        yield ()
        return
    first, tail = items[0], items[1:]
    for pi in partitions(tail):
        yield ((first,),) + pi
        for j in range(len(pi)):
            yield pi[:j] + ((first,) + pi[j],) + pi[j + 1:]


def connected(n, edges):
    if n == 1:
        return True
    seen = {0}
    while True:
        new = set(seen)
        for a, b in edges:
            if a in seen:
                new.add(b)
            if b in seen:
                new.add(a)
        if new == seen:
            return len(seen) == n
        seen = new


@lru_cache(None)
def connected_pair_graphs(n):
    pairs = tuple(it.combinations(range(n), 2))
    out = []
    for mask in range(1 << len(pairs)):
        edges = tuple(pairs[j] for j in range(len(pairs)) if mask >> j & 1)
        if connected(n, edges):
            out.append(edges)
    return tuple(out)


def host_data(n, edges):
    A = [[0] * n for _ in range(n)]
    for a, b in edges:
        assert a != b
        A[a][b] = A[b][a] = 1
    p = F(len(edges), math.comb(n, 2))
    assert p >= F(1, 2)
    M = [[F(0) if a == b else F(A[a][b], 1) / p - 1
          for b in range(n)] for a in range(n)]
    assert sum(map(sum, M)) == 0
    return A, p, M


def direct_activity(s, source_edges, M, z):
    n = len(M)
    source_edges = frozenset(tuple(sorted(e)) for e in source_edges)
    cgraphs = connected_pair_graphs(s)
    total = F(0)
    for labels in it.product(range(n), repeat=s):
        f = {}
        for a, b in it.combinations(range(s), 2):
            f[a, b] = -F(labels[a] == labels[b])
            if (a, b) in source_edges:
                f[a, b] += z * M[labels[a]][labels[b]]
        for edges in cgraphs:
            prod = F(1)
            for edge in edges:
                prod *= f[edge]
                if not prod:
                    break
            total += prod
    return total / n ** s


def contracted_activity(s, source_edges, M, z):
    n = len(M)
    source_edges = tuple(tuple(sorted(e)) for e in source_edges)

    @lru_cache(None)
    def quotient_density(r, qedges):
        ans = F(0)
        for labels in it.product(range(n), repeat=r):
            prod = F(1)
            for a, b in qedges:  # duplicates deliberately retained
                prod *= M[labels[a]][labels[b]]
            ans += prod
        return ans / n ** r

    answer = F(0)
    for pi in partitions(range(s)):
        r = len(pi)
        where = {v: j for j, block in enumerate(pi) for v in block}
        mobius = math.prod((-1) ** (len(b) - 1) * math.factorial(len(b) - 1)
                          for b in pi)
        for mask in range(1 << len(source_edges)):
            selected = [source_edges[j] for j in range(len(source_edges))
                        if mask >> j & 1]
            if any(where[a] == where[b] for a, b in selected):
                continue
            qedges = tuple(sorted(tuple(sorted((where[a], where[b])))
                                  for a, b in selected))
            if not connected(r, qedges):
                continue
            answer += (F(mobius, n ** (s - r)) * z ** len(selected)
                       * quotient_density(r, qedges))
    return answer


def xi_direct(s, source_edges, M, z):
    n = len(M)
    source_edges = frozenset(tuple(sorted(e)) for e in source_edges)
    ans = F(0)
    for labels in it.product(range(n), repeat=s):
        prod = F(1)
        for a, b in it.combinations(range(s), 2):
            fac = F(labels[a] != labels[b])
            if (a, b) in source_edges:
                fac += z * M[labels[a]][labels[b]]
            prod *= fac
        ans += prod
    return ans / n ** s


def activity_checks():
    hosts = [
        host_data(4, [(0, 1), (1, 2), (2, 3)]),
        host_data(5, [(i, (i + 1) % 5) for i in range(5)]),
        host_data(5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (2, 3)]),
    ]
    sources = [
        (3, [(0, 1), (0, 2)]),
        (4, [(0, 1), (1, 2), (2, 3)]),
        (4, [(0, 1), (0, 2), (0, 3)]),
        (4, [(0, 1), (1, 2), (2, 3), (0, 3)]),
    ]
    comparisons = 0
    for A, p, M in hosts:
        n = len(A)
        for s, edges in sources:
            for z in [F(0), F(1, 2), F(1)]:
                direct = direct_activity(s, edges, M, z)
                contract = contracted_activity(s, edges, M, z)
                assert direct == contract, (n, s, edges, z, direct, contract)
                comparisons += 1
                if z == 0:
                    assert direct == F((-1) ** (s - 1) * math.factorial(s - 1), n ** (s - 1))
                if s == 3:
                    rowsums = list(map(sum, M))
                    formula = (F(2, n * n) + z * z / n ** 3
                               * (sum(r * r for r in rowsums)
                                  - sum(t * t for row in M for t in row)))
                    assert direct == formula
        # Check the full polymer identity, including all subsets, on Q_2.
        s, edges = sources[-1]
        es = set(edges)
        for z in [F(0), F(1, 2), F(1)]:
            w = {}
            for size in range(2, s + 1):
                for U in it.combinations(range(s), size):
                    local = [(i, j) for i in range(size) for j in range(i + 1, size)
                             if tuple(sorted((U[i], U[j]))) in es]
                    w[U] = contracted_activity(size, local, M, z)
            gas = F(0)
            for pi in partitions(range(s)):
                gas += math.prod(w[tuple(sorted(b))] for b in pi if len(b) >= 2)
            xi = xi_direct(s, edges, M, z)
            assert xi == gas
            if z == 0:
                assert xi == F(math.prod(range(n - s + 1, n + 1)), n ** s)
            if z == 1:
                inj = sum(all(A[f[a]][f[b]] for a, b in edges)
                          for f in it.permutations(range(n), s))
                assert xi == F(inj, n ** s) / p ** len(edges)
    print(f"Exact signed contraction: {comparisons} direct connected-graph / quotient-multigraph comparisons passed.")
    print("Exact Xi / polymer / ordinary injective-count identities passed for three hosts and z=0,1/2,1.")
    return hosts


def star_resummation_checks(hosts):
    count = 0
    for A, p, M in hosts:
        n = len(A)
        for z in [F(0), F(1, 2), F(1)]:
            max_r = 10
            numerator = [F(0)] * (max_r + 1)
            for x in range(n):
                poly = [F(1)] + [F(0)] * max_r
                for y in range(n):
                    if x == y:
                        continue
                    a = (1 + z * M[x][y]) / n
                    for j in range(max_r, 0, -1):
                        poly[j] += a * poly[j - 1]
                numerator = [a + b / n for a, b in zip(numerator, poly)]
            den = [F(math.comb(n, j), n ** j) if j <= n else F(0)
                   for j in range(max_r + 1)]
            series = [F(0)] * (max_r + 1)
            for r in range(max_r + 1):
                series[r] = numerator[r] - sum(den[j] * series[r - j]
                                               for j in range(1, r + 1))
            for r in range(1, 4):
                literal = direct_activity(r + 1, [(0, j) for j in range(1, r + 1)], M, z)
                assert literal == math.factorial(r) * series[r]
                count += 1
            if z == 1:
                degrees = list(map(sum, A))
                for r in range(max_r + 1):
                    coeff = sum(F(math.comb(deg, r), 1) / (p * n) ** r
                                for deg in degrees if deg >= r) / n
                    assert numerator[r] == coeff
                    # Full core positivity, including zero beyond available degree.
                    assert math.factorial(r) * numerator[r] >= 0
    print(f"Whole-star resummation: {count} connected-activity checks; degree-mixture coefficients checked through order 10.")


def gram_checks():
    # Verify the polynomial remainder identity exactly, not only on positive differences.
    grid = [F(i, 8) for i in range(9)]
    identities = 0
    for d in range(2, 31):
        for a, x in it.product(grid, repeat=2):
            rem = sum((i + 1) * a ** i * x ** (d - 2 - i) for i in range(d - 1))
            assert x ** d - a ** d - d * a ** (d - 1) * (x - a) == (x - a) ** 2 * rem
            assert rem >= 0
            identities += 1
    # Exact Walsh example: a balanced column system, with independent selected rows.
    M, n = 8, 7
    A = [[(1 + (-1) ** ((x & y).bit_count())) // 2 for y in range(1, n + 1)]
         for x in range(M)]
    q = [F(sum(A[i][v] for i in range(M)), M) for v in range(n)]
    D = [[F(A[i][v]) - q[v] for v in range(n)] for i in range(M)]
    R = [[sum(D[i][v] * D[i][w] for i in range(M)) / M
          for w in range(n)] for v in range(n)]
    codeg = [[F(sum(A[i][v] * A[i][w] for i in range(M)), M)
              for w in range(n)] for v in range(n)]
    for d in range(2, 13):
        mu = sum(x ** d for x in q)
        var = sum(codeg[v][w] ** d for v in range(n) for w in range(n)) - mu * mu
        avec = [x ** (d - 1) for x in q]
        gram = d * sum(avec[v] * R[v][w] * avec[w] for v in range(n) for w in range(n))
        rem = sum(R[v][w] ** 2 * sum((i + 1) * (q[v] * q[w]) ** i
                                    * codeg[v][w] ** (d - 2 - i) for i in range(d - 1))
                  for v in range(n) for w in range(n))
        assert gram >= 0 and rem >= 0 and var == gram + rem
        kappa_squared = F(M, 4 * (M + n))
        assert var <= 25 * kappa_squared * F(n, 2 ** d)
        if d <= 5:
            vals = [sum(all(A[i][v] for i in rows) for v in range(n))
                    for rows in it.product(range(M), repeat=d)]
            em = F(sum(vals), len(vals))
            ev = F(sum(t * t for t in vals), len(vals)) - em * em
            assert em == mu and ev == var
    # Irregular balanced columns: check the same exact identity numerically.
    rng = np.random.default_rng(181)
    M, n = 128, 120
    A = np.zeros((M, n), dtype=float)
    for v in range(n):
        count = M // 2 + (v % 3) - 1
        A[rng.choice(M, count, replace=False), v] = 1
    q = A.mean(axis=0)
    D = A - q[None, :]
    R = D.T @ D / M
    codeg = A.T @ A / M
    kappa2 = np.linalg.norm(D, 2) ** 2 / (M + n)
    aa = q[:, None] * q[None, :]
    for d in range(2, 7):
        assert np.max(np.abs(q - .5)) <= 1 / (20 * d)
        mu = np.sum(q ** d)
        var = np.sum(codeg ** d) - mu ** 2
        avec = q ** (d - 1)
        gram = d * (avec @ R @ avec)

        rem = np.sum(R ** 2 * sum((i + 1) * aa ** i * codeg ** (d - 2 - i)
                                 for i in range(d - 1)))
        assert gram >= -1e-9 and rem >= -1e-9
        assert abs(var - gram - rem) < 1e-8 * max(1, var)
        assert .9 * n / 2 ** d <= mu <= (10 / 9) * n / 2 ** d
        assert var <= 25 * kappa2 * n / 2 ** d
    print(f"All-orders Gram lemma: {identities} exact polynomial checks; exact moments through d=12 and irregular-column checks passed.")


def star_load_checks():
    # Nonzero symplectic host: n=2^(2r)-1, regular degree (n+1)/2.
    # Its centred norm is <= sqrt(n) for the sizes below. Only its exact
    # degree-mixture coefficients are needed; no huge adjacency matrix is built.
    checked = 0
    largest_ratio = 0.0
    for bits in [16, 20, 30]:
        n = (1 << bits) - 1
        degree = (n + 1) // 2
        p = F(degree, n - 1)
        for d in range(1, 51):
            if n < 500 * d * d:
                continue
            numerator = [F(math.comb(degree, r), 1) / (p * n) ** r
                         for r in range(d + 1)]
            den = [F(math.comb(n, r), n ** r) for r in range(d + 1)]
            coef = [F(0)] * (d + 1)
            for r in range(d + 1):
                coef[r] = numerator[r] - sum(den[j] * coef[r - j]
                                              for j in range(1, r + 1))
            R = 2 * math.e * d
            Mstar = 160 * R * R / n  # L=1, so 80(L^2+1)=160
            load = 0.0
            for r in range(1, d + 1):
                assert float(abs(coef[r])) <= Mstar / R ** r
                activity = abs(coef[r] * math.factorial(r))
                load += (r + 1) * math.comb(d, r) * math.exp(r) * float(activity)
            bound = 16000 * d * d / n
            assert load <= bound
            largest_ratio = max(largest_ratio, load / bound)
            checked += 1
    pruning_checks = 0
    for d in range(1, 1001):
        h = 1 << d
        assert d ** 3 <= 4 * h
        assert 8 * d * d <= 9 * h
        for k2 in [F(0), F(1, 4), F(1), F(100)]:
            N = 4 * 10 ** 9 * (k2 + 1) * h
            delta = N / (1000 * d)
            deleted = 10 ** 6 * k2 * d * d
            nlow = N - deleted
            assert deleted <= delta
            assert nlow >= N / 2 and nlow - 1 >= N / 3
            assert F(1, 2) - 2 * delta / (nlow - 1) >= F(1, 3)
            assert 4 * delta <= nlow / (72 * d)  # p'>=1/3 and e<3
            assert 4 * N <= 9 * nlow  # re-centred operator factor <3K
            assert nlow >= 500 * d * d
            star_bound = 8000 * (9 * k2 + 1) * d * d / nlow
            linear_bound = 162000 * (k2 + 1) * h / N
            assert star_bound <= linear_bound < F(1, 1000)
            pruning_checks += 1
    print(f"Linear-scale star-load lemma: {checked} exact coefficient sequences through order 50; max load/bound={largest_ratio:.6g}; {pruning_checks:,} exact pruning-constant checks passed.")


def support_checks():
    count = 0
    for d in range(1, 6):
        vertices = [v for v in range(1 << d) if v.bit_count() % 2 == 0]
        m = len(vertices)
        adj = [sum(1 << j for j, w in enumerate(vertices)
                   if (v ^ w).bit_count() == 2) for v in vertices]
        ec = [0] * (1 << m)
        alpha = [0] * (1 << m)
        for mask in range(1, 1 << m):
            low = mask & -mask
            i = low.bit_length() - 1
            prev = mask ^ low
            ec[mask] = ec[prev] + (adj[i] & prev).bit_count()
            alpha[mask] = max(alpha[prev], 1 + alpha[prev & ~adj[i]])
            t = mask.bit_count()
            assert (1 << (2 * ec[mask])) <= t ** ((d - 1) * t)
            assert alpha[mask] * (2 * ec[mask] + t) >= t * t
            count += 1
    isocount = 0
    for d in range(1, 5):
        n = 1 << d
        adj = [sum(1 << (v ^ (1 << j)) for j in range(d)) for v in range(n)]
        ec = [0] * (1 << n)
        for mask in range(1, 1 << n):
            low = mask & -mask
            i = low.bit_length() - 1
            prev = mask ^ low
            ec[mask] = ec[prev] + (adj[i] & prev).bit_count()
            t = mask.bit_count()
            assert (1 << (2 * ec[mask])) <= t ** t
            isocount += 1
    print(f"Cube support bounds: {count:,} parity supports (through Q_5), with exact independence-number checks; {isocount:,} edge-isoperimetric supports passed.")


def constant_checks():
    checked = 0
    min_hall_ratio = float("inf")
    max_scaled_load = 0.0
    for d in range(2, 10001):
        for kappa in [4.0, 10.0, 100.0]:
            for mult in [1.0, 10.0, 1e10]:
                C = mult * 1e6 * kappa * kappa * d * d
                k = math.ceil(8 * math.log(C) + 20)
                load = 1500 * kappa * kappa * d / C + 5 / C + 2 * C * d * 2.0 ** (-k)
                assert load < 1 / (100 * d)
                assert 2 * load < 1 / d
                hall = C / (6 * k * (1 + d * math.log2(C)))
                assert hall > 1
                assert k <= 10 * math.log(C)
                assert math.log(C) ** 2 <= 3 * math.sqrt(C)
                min_hall_ratio = min(min_hall_ratio, hall)
                max_scaled_load = max(max_scaled_load, d * load)
                checked += 1
    for k in range(20, 1001):
        assert math.factorial(k - 1) >= 4 ** k
    collision_load = math.e / (8 - math.e)
    assert collision_load < 1 - math.exp(-1)
    assert math.e / (2e9 - math.e) < 1e-6  # pruned linear-scale edgeless supports
    print(f"Constants: {checked:,} parameter checks through d=10,000; max d*load={max_scaled_load:.6g}, min Hall margin={min_hall_ratio:.6g}.")
    print(f"Pure-collision load at N=8h: {collision_load:.9f} < {1-math.exp(-1):.9f}.")


def symplectic_swap(x, bits):
    y = 0
    for j in range(0, bits, 2):
        y |= ((x >> j) & 1) << (j + 1)
        y |= ((x >> (j + 1)) & 1) << j
    return y


def actual_embedding_checks():
    """Produce literal injective cube certificates, without claiming a new range.

    The host on F_2^(2r) has adjacency 1 iff the alternating pairing is 1.
    It has actual p=1/2 and B=(I-H)/2, HH^T=N I. Thus it satisfies the exact
    benchmark spectral convention with K <= (1+N^(-1/2))/2.
    """
    # Independently check the Hadamard and zero-diagonal conventions at N=64.
    bits, N = 6, 64
    mates = [symplectic_swap(x, bits) for x in range(N)]
    H = np.array([[1 - 2 * ((mates[x] & y).bit_count() % 2)
                   for y in range(N)] for x in range(N)], dtype=np.int64)
    assert np.array_equal(H @ H.T, N * np.eye(N, dtype=np.int64))
    A = (1 - H) // 2
    assert np.all(np.diag(A) == 0)
    assert int(A.sum()) == N * (N - 1) // 2

    rng = random.Random(1812026)
    certificates = []
    for d in [4, 5, 6, 7]:
        bits = d + 6
        bits += bits % 2
        N = 1 << bits
        M = n = N // 2
        h = 1 << d
        X = [x for x in range(h) if x.bit_count() % 2 == 0]
        Y = [y for y in range(h) if y.bit_count() % 2]
        source_neighbours = [[y ^ (1 << j) for j in range(d)] for y in Y]
        all_bits = (1 << n) - 1
        ell = F(n, 2 * h)
        row_cache = {}

        def row_mask(x):
            if x not in row_cache:
                mate = symplectic_swap(x, bits)
                mask = 0
                for j in range(n):
                    if (mate & (M + j)).bit_count() % 2:
                        mask |= 1 << j
                row_cache[x] = mask
            return row_cache[x]

        success = False
        for attempt in range(1, 201):
            f = dict(zip(X, rng.sample(range(M), len(X))))
            lists = []
            for nb in source_neighbours:
                mask = all_bits
                for x in nb:
                    mask &= row_mask(f[x])
                lists.append(mask)
            row_min = min(mask.bit_count() for mask in lists)
            if row_min < ell:
                continue
            loads = [0] * n
            for mask in lists:
                while mask:
                    bit = mask & -mask
                    loads[bit.bit_length() - 1] += 1
                    mask ^= bit
            col_max = max(loads)
            if col_max >= ell:
                continue
            owner = [-1] * n
            chosen = [-1] * len(Y)

            def augment(i, seen):
                mask = lists[i]
                while mask:
                    bit = mask & -mask
                    j = bit.bit_length() - 1
                    mask ^= bit
                    if j in seen:
                        continue
                    seen.add(j)
                    if owner[j] < 0 or augment(owner[j], seen):
                        owner[j] = i
                        chosen[i] = j
                        return True
                return False

            assert all(augment(i, set()) for i in range(len(Y)))
            for i, y in enumerate(Y):
                f[y] = M + chosen[i]
            image = [f[x] for x in range(h)]
            assert len(set(image)) == h
            for x in range(h):
                for j in range(d):
                    y = x ^ (1 << j)
                    assert (symplectic_swap(image[x], bits) & image[y]).bit_count() % 2 == 1
            certificates.append({
                "d": d, "N": N, "host_rule": "alternating_binary_pairing_equals_one",
                "bits": bits, "p": "1/2", "spectral_K_upper": (1 + N ** -.5) / 2,
                "attempts": attempt, "minimum_row_degree": row_min,
                "maximum_column_degree": col_max, "image_in_source_integer_order": image,
            })
            print(f"Actual Q_{d} certificate: N={N}, row minimum={row_min}, column maximum={col_max}, attempts={attempt}; all edges and all distinct images checked.")
            success = True
            break
        assert success, (d, N)
    (ROOT / "CubeSpectralEmbeddingCertificates.json").write_text(json.dumps(certificates, indent=2) + "\n")


def main():
    print("Spectral cube verification: checks of the proved lemmas, not a proof of the constant-multiplier benchmark.")
    check_spec()
    hosts = activity_checks()
    star_resummation_checks(hosts)
    gram_checks()
    star_load_checks()
    support_checks()
    constant_checks()
    actual_embedding_checks()
    print("Spec.lean SHA-256 unchanged:", check_spec())
    print("All checks passed. The proved general bound is 10^6(K+4)^2 d^2 2^d; the factor d^2 remains.")


if __name__ == "__main__":
    main()
