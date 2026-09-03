#!/usr/bin/env python3
"""Finite checks for CubeDirectRamseyProgress.md.

No test asserts that the terminal robust core forces a cube. The new theorems
are paper proofs. All embedding certificates use ordinary injective copies.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
from math import comb, exp, isqrt, log, sqrt
from pathlib import Path
import hashlib
import random
import time

import numpy as np

SPEC_HASH = "9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b"
RNG = random.Random(1814096)
NRNG = np.random.default_rng(1814096)
COUNTS = Counter()


def members(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def subsets(mask):
    sub = mask
    while True:
        yield sub
        if not sub:
            return
        sub = (sub - 1) & mask


def bit_host(n, mask):
    adj = [0] * n
    for i, (u, v) in enumerate(combinations(range(n), 2)):
        if mask >> i & 1:
            adj[u] |= 1 << v
            adj[v] |= 1 << u
    return adj


def degree(adj, u, S, color):
    assert not (S >> u & 1)
    red = (adj[u] & S).bit_count()
    return red if color else S.bit_count() - red


def edge_count(adj, A, B, color):
    return sum(degree(adj, u, B, color) for u in members(A))


def audit_copy(red, d, image, color):
    h = 1 << d
    assert len(image) == h and len(set(image)) == h
    for x in range(h):
        for j in range(d):
            y = x ^ (1 << j)
            if x < y:
                assert bool(red[image[x], image[y]]) == bool(color)
                COUNTS['verified_cube_edges'] += 1
    for i, j in combinations(range(d), 2):
        for x in range(h):
            if not (x >> i & 1) and not (x >> j & 1):
                cycle = [x, x ^ (1 << i), x ^ (1 << i) ^ (1 << j),
                         x ^ (1 << j)]
                assert len({image[v] for v in cycle}) == 4
                assert (cycle[1] ^ (1 << j)) == (cycle[3] ^ (1 << i))
                for k in range(4):
                    assert bool(red[image[cycle[k]],
                                    image[cycle[(k + 1) % 4]]]) == bool(color)
                COUNTS['verified_cube_squares'] += 1
    COUNTS['injective_cube_certificates'] += 1


def complete_one_sided(red, d, D, left, right, color):
    h, m = 1 << d, 1 << (d - 1)
    assert len(left) >= m and len(right) >= m + d * D
    assert set(left).isdisjoint(right)
    left = list(left[:m])
    right = np.array(right, dtype=np.int64)
    assert all(np.count_nonzero(red[u, right] != color) <= D for u in left)
    image = [-1] * h
    even = [v for v in range(h) if v.bit_count() % 2 == 0]
    odd = [v for v in range(h) if v.bit_count() % 2]
    for x, u in zip(even, left):
        image[x] = u
    used = np.zeros(len(right), dtype=bool)
    for y in odd:
        valid = ~used
        raw = np.ones(len(right), dtype=bool)
        for j in range(d):
            u = image[y ^ (1 << j)]
            assert u >= 0
            raw &= red[u, right] == color
        assert int(raw.sum()) >= m
        valid &= raw
        pos = np.flatnonzero(valid)
        assert len(pos)
        i = int(pos[0])
        used[i] = True
        image[y] = int(right[i])
    audit_copy(red, d, image, color)
    return image


def check_small_completion():
    # All rectangular colorings in these four configurations.
    for d, D, a, b in [(1, 0, 2, 1), (1, 1, 2, 2),
                       (2, 0, 2, 2), (2, 1, 3, 4)]:
        m = 1 << (d - 1)
        for mask in range(1 << (a * b)):
            red = np.zeros((a + b, a + b), dtype=bool)
            for u in range(a):
                for v in range(b):
                    red[u, a + v] = red[a + v, u] = bool(mask >> (u * b + v) & 1)
            for color in (0, 1):
                if all(np.count_nonzero(red[u, a:] != color) <= D
                       for u in range(a)):
                    for left in combinations(range(a), m):
                        complete_one_sided(red, d, D, left,
                                           list(range(a, a + b)), color)
                        COUNTS['small_one_sided_instances'] += 1
            COUNTS['rectangular_colorings'] += 1


def check_cut_identities():
    # Independently minimize over P,Z, and compare with the explicit high-row
    # count. Also minimize the edge/vertex cost and compare with its capped sum.
    n = 4
    U = (1 << n) - 1
    alphas = [F(0), F(1, 8), F(1, 3), F(1, 2)]
    for mask in range(1 << comb(n, 2)):
        adj = bit_host(n, mask)
        for A in subsets(U):
            a = A.bit_count()
            if not a or 2 * a > n:
                continue
            outside = U ^ A
            for c in (0, 1):
                for D in range(3):
                    cap_num = sum(min(D + 1, degree(adj, v, A, c))
                                  for v in members(outside))
                    kappa_formula = n + 1
                    kappa_brute = n + 1
                    edge_vertex_min = (D + 1) * (n + 1)
                    for Z in subsets(outside):
                        B = outside ^ Z
                        high = sum(1 << v for v in members(A)
                                   if degree(adj, v, B, c) > D)
                        p, z = high.bit_count(), Z.bit_count()
                        E = edge_count(adj, A, B, c)
                        assert (D + 1) * p <= E
                        kappa_formula = min(kappa_formula, p + z)
                        edge_vertex_min = min(edge_vertex_min, (D + 1) * z + E)
                        for P in subsets(A):
                            if all(degree(adj, v, B, c) <= D
                                   for v in members(A ^ P)):
                                kappa_brute = min(kappa_brute, P.bit_count() + z)
                        for alpha in alphas:
                            if p + z <= alpha * a:
                                g, w = a - p, p + z
                                assert g > 0
                                assert w * (1 - alpha) <= alpha * g
                                assert (a + z) * (1 - alpha) <= g
                                assert B.bit_count() >= (1 - alpha) * n / 2
                                COUNTS['admissible_cut_accounting'] += 1
                        COUNTS['cut_Z_tests'] += 1
                    assert edge_vertex_min == cap_num
                    assert kappa_brute == kappa_formula
                    assert (D + 1) * kappa_formula <= cap_num
                    COUNTS['cut_cost_minima'] += 1


def check_all_K6():
    # General theorem with alpha=0, D=0, d=2: N=(h-2)+2m=6.
    # Cut resilience in this case is precisely connectivity in both colors.
    n, U0, m = 6, (1 << 6) - 1, 2
    for mask in range(1 << comb(n, 2)):
        adj = bit_host(n, mask)
        U = U0
        pools = [[], []]
        while True:
            found = None
            for A in subsets(U):
                if not A or 2 * A.bit_count() > U.bit_count():
                    continue
                B = U ^ A
                for wrong in (0, 1):
                    if all(degree(adj, u, B, wrong) == 0 for u in members(A)):
                        found = A, B, 1 - wrong
                        break
                if found:
                    break
            if found is None:
                assert U.bit_count() >= 4
                for color in (0, 1):
                    reached = U & -U
                    frontier = reached
                    while frontier:
                        u = (frontier & -frontier).bit_length() - 1
                        frontier &= frontier - 1
                        nb = ((adj[u] if color else ~(adj[u] | (1 << u))) & U)
                        new = nb & ~reached
                        reached |= new
                        frontier |= new
                    assert reached == U
                assert sum(map(len, pools)) <= 2
                for color in (0, 1):
                    assert all(degree(adj, u, U, 1 - color) == 0
                               for u in pools[color])
                COUNTS['K6_terminal_core'] += 1
                break
            A, B, color = found
            assert B.bit_count() >= m
            pools[color].extend(members(A))
            U = B
            COUNTS['K6_peeling_steps'] += 1
            if len(pools[color]) >= m:
                left = pools[color][:m]
                right = list(members(U))[:m]
                assert len(set(left + right)) == 4
                assert all(degree(adj, u, 1 << v, color) == 1
                           for u in left for v in right)
                COUNTS['K6_constructed_C4'] += 1
                break
            assert sum(map(len, pools)) <= 2
            assert U.bit_count() >= 4
        COUNTS['K6_colorings'] += 1


def check_sampled_full_extractions():
    # Nonzero-alpha and nonzero-D cases, with exhaustive cut searches on each
    # sampled host. Terminal cores are independently tested by deleting a
    # single combined set T=P union Z, not by reusing the cut-search routine.
    for d, D, alpha, n in [(2, 0, F(1, 3), 9), (2, 1, F(0), 10),
                            (1, 1, F(1, 4), 6)]:
        h, m = 1 << d, 1 << (d - 1)
        M = m + d * D
        assert (1 - alpha) * n >= h - 2 + 2 * M
        all_pairs = list(combinations(range(n), 2))
        for trial in range(256):
            if trial % 4 == 0:
                # Unrestricted dense samples, frequently ending at a core.
                mask = RNG.getrandbits(len(all_pairs))
            elif trial % 4 == 1:
                # Biased, but still independent, samples.
                mask = sum(1 << i for i, _ in enumerate(all_pairs)
                           if RNG.random() < 0.15)
            else:
                # Many unbounded-type threshold cuts, then a few edits.
                row_colors = [RNG.randrange(2) for _ in range(n)]
                mask = sum(1 << i for i, (u, v) in enumerate(all_pairs)
                           if row_colors[u] ^ (RNG.random() < 0.04))
            adj = bit_host(n, mask)
            U = (1 << n) - 1
            pools = [[], []]
            waste = set()
            while True:
                found = None
                for A in subsets(U):
                    a = A.bit_count()
                    if not a or 2 * a > U.bit_count():
                        continue
                    outside = U ^ A
                    budget = (alpha * a).__floor__()
                    outside_list = list(members(outside))
                    for z in range(budget + 1):
                        for labels in combinations(outside_list, z):
                            Z = sum(1 << v for v in labels)
                            B = outside ^ Z
                            for wrong in (0, 1):
                                P = sum(1 << v for v in members(A)
                                        if degree(adj, v, B, wrong) > D)
                                if P.bit_count() + z <= alpha * a:
                                    found = A, P, Z, B, wrong
                                    break
                            if found:
                                break
                        if found:
                            break
                    if found:
                        break
                if found is None:
                    for A in subsets(U):
                        a = A.bit_count()
                        if not a or 2 * a > U.bit_count():
                            continue
                        for k in range((alpha * a).__floor__() + 1):
                            for labels in combinations(list(members(U)), k):
                                T = sum(1 << v for v in labels)
                                G = A & ~T
                                B = U & ~(A | T)
                                for wrong in (0, 1):
                                    assert any(degree(adj, v, B, wrong) > D
                                               for v in members(G))
                                    COUNTS['independent_terminal_cut_tests'] += 1
                    assert U.bit_count() >= F(n) - F(h - 2, 1 - alpha)
                    COUNTS['sampled_terminal_core'] += 1
                    break
                A, P, Z, B, wrong = found
                G = A ^ P
                assert B.bit_count() >= M
                color = 1 - wrong
                pools[color].extend(members(G))
                waste.update(members(P | Z))
                U = B
                total = sum(map(len, pools))
                assert len(waste) * (1 - alpha) <= alpha * total
                assert n - U.bit_count() == total + len(waste)
                for c in (0, 1):
                    assert all(degree(adj, v, U, 1 - c) <= D for v in pools[c])
                if len(pools[color]) >= m:
                    red = np.zeros((n, n), dtype=bool)
                    for u in range(n):
                        for v in members(adj[u]):
                            red[u, v] = True
                    complete_one_sided(red, d, D, pools[color],
                                       list(members(U)), color)
                    COUNTS['sampled_extracted_cubes'] += 1
                    break
                assert total <= h - 2
                assert U.bit_count() >= F(2 * M, 1 - alpha)
            COUNTS['sampled_full_extractions'] += 1


def random_symmetric(n):
    top = np.triu(NRNG.integers(0, 2, size=(n, n), dtype=np.uint8), 1)
    return (top | top.T).astype(bool)


def verify_chain_step(red, old_U, A, P, Z, wrong, D, alpha):
    B = sorted(set(old_U) - set(A) - set(Z))
    assert 0 < len(A) <= len(old_U) / 2
    assert set(P).issubset(A)
    assert set(A).isdisjoint(Z)
    assert set(A).union(Z).issubset(old_U)
    assert len(P) + len(Z) <= alpha * len(A)
    good = sorted(set(A) - set(P))
    assert all(np.count_nonzero(red[u, B] == wrong) <= D for u in good)
    g, w = len(good), len(P) + len(Z)
    assert w * (1 - alpha) <= alpha * g
    assert len(B) >= (1 - alpha) * len(old_U) / 2
    COUNTS['nonzero_parameter_chain_steps'] += 1
    COUNTS['actual_separator_vertices'] += len(Z)
    COUNTS['actual_bad_row_vertices'] += len(P)
    return B, good


def check_noisy_chains():
    # Blocks have arbitrary internal edges. Bad rows can have linear wrong
    # degree; good rows have D errors directed at the same future core hubs.
    # This deliberately does not impose a reverse maximum-degree bound.
    for d, style in [(2, 'blocks'), (3, 'blocks'), (4, 'blocks'),
                     (7, 'blocks'), (8, 'blocks'), (10, 'blocks'),
                     (7, 'singletons')]:
        h, m = 1 << d, 1 << (d - 1)
        n, D, alpha = 5 * h // 2, h // (16 * d), F(1, 8)
        M = m + d * D
        assert (1 - alpha) * n >= h - 2 + 2 * M
        red = random_symmetric(n)
        U = list(range(n))
        pools = [[], []]
        waste = []
        records = []
        step = 0
        while True:
            a = 1 if style == 'singletons' else max(1, m // 4)
            cost = a // 8
            p, z = cost // 2, cost - cost // 2
            A, Z = U[:a], U[a:a + z]
            P = A[:p]
            good = A[p:]
            B = U[a + z:]
            assert len(B) >= M
            wrong, color = step % 2, 1 - step % 2
            # Make bad rows truly bad, and put D errors at shared core hubs
            # for every other row. No constraints inside A or Z are used.
            for u in A:
                red[u, B] = red[B, u] = bool(color)
            for u in P:
                red[u, B] = red[B, u] = bool(wrong)
            hubs = B[-D:] if D else []
            for u in good:
                red[u, hubs] = red[hubs, u] = bool(wrong)
            records.append((list(U), list(A), list(P), list(Z), wrong))
            pools[color].extend(good)
            waste.extend(P + Z)
            U = B
            total_good = sum(map(len, pools))
            assert len(waste) * (1 - alpha) <= alpha * total_good
            assert n - len(U) == total_good + len(waste)
            if len(pools[color]) >= m:
                # Recheck the entire supplied chain against the final graph,
                # so a later edit cannot silently invalidate an earlier cut.
                for old_U, old_A, old_P, old_Z, old_wrong in records:
                    verify_chain_step(red, old_U, old_A, old_P, old_Z,
                                      old_wrong, D, alpha)
                for c in (0, 1):
                    assert all(np.count_nonzero(red[u, U] != c) <= D
                               for u in pools[c])
                if style == 'singletons':
                    assert len(records) == h - 1
                    assert not waste
                    # Phi= D/(D+1) at each singleton cut here; it need not
                    # be <=alpha although the actual degree cut has no waste.
                    assert D / (D + 1) > alpha
                    COUNTS['long_zero_waste_steps'] += len(records)
                complete_one_sided(red, d, D, pools[color], U, color)
                COUNTS['noisy_chain_cubes'] += 1
                break
            assert total_good <= h - 2
            assert len(U) >= F(n) - F(h - 2, 1 - alpha)
            assert len(U) >= F(2 * M, 1 - alpha)
            step += 1


def check_total_error_chains():
    # Evaluate the aggregate scalar certificate independently of the adaptive
    # stopping rule. All ten cuts are supplied even if a cube existed earlier.
    for d in (4, 7, 8):
        h, m = 1 << d, 1 << (d - 1)
        n, D = 5 * h // 2, h // (16 * d)
        red = random_symmetric(n)
        U = list(range(n))
        records = []
        a = max(1, m // 4)
        for i in range(10):
            p = a // 16
            z = a // 16
            A, Z, B = U[:a], U[a:a + z], U[a + z:]
            color = i % 2
            for u in A:
                red[u, B] = red[B, u] = bool(color)
            for u in A[:p]:
                targets = B[-(D + 1):]
                red[u, targets] = red[targets, u] = bool(1 - color)
            records.append((list(A), list(Z), list(B), color))
            U = B
        assert len(U) >= m + d * D
        total_A, total_E, total_Z = 0, 0, 0
        pools = [[], []]
        for A, Z, B, color in records:
            E = sum(int(np.count_nonzero(red[u, B] != color)) for u in A)
            low = [u for u in A if np.count_nonzero(red[u, B] != color) <= D]
            b_i = max(0, len(A) - E // (D + 1))
            assert len(low) >= b_i
            pools[color].extend(low)
            total_A += len(A)
            total_E += E
            total_Z += len(Z)
            COUNTS['aggregate_error_cuts'] += 1
        assert F(total_A) - F(total_E, D + 1) > h - 2
        assert n - len(U) - total_Z == total_A
        color = max(range(2), key=lambda c: len(pools[c]))
        assert len(pools[color]) >= m
        complete_one_sided(red, d, D, pools[color], U, color)
        COUNTS['aggregate_error_chain_cubes'] += 1


def check_hierarchies_and_separators():
    for d in range(1, 9):
        h, m = 1 << d, 1 << (d - 1)
        n = 2 * h - 2
        for style in ('balanced', 'comb', 'random'):
            red = np.zeros((n, n), dtype=bool)

            def build(vertices):
                if len(vertices) == 1:
                    return vertices, None, None, None
                if style == 'balanced':
                    k = len(vertices) // 2
                elif style == 'comb':
                    k = 1
                else:
                    k = RNG.randrange(1, len(vertices))
                left, right = vertices[:k], vertices[k:]
                color = RNG.randrange(2)
                red[np.ix_(left, right)] = bool(color)
                red[np.ix_(right, left)] = bool(color)
                return vertices, build(left), build(right), color

            node = build(list(range(n)))
            pools = [[], []]
            while True:
                vertices, left, right, color = node
                assert left is not None and right is not None
                if len(left[0]) > len(right[0]):
                    left, right = right, left
                A, B = left[0], right[0]
                assert len(B) >= m
                pools[color].extend(A)
                COUNTS['hierarchical_peeling_steps'] += 1
                if len(pools[color]) >= m:
                    complete_one_sided(red, d, 0, pools[color], B, color)
                    COUNTS['hierarchical_cube_certificates'] += 1
                    break
                assert sum(map(len, pools)) <= h - 2
                assert len(B) >= h
                node = right

    # Directly check the balanced-component-to-cut size conversion, including
    # nonempty exceptional separators. No graph-theoretic search is used here.
    for t in range(2, 301):
        for s in range(t // 32 + 1):
            for _ in range(10):
                remain = t - s
                parts = []
                while remain:
                    part = RNG.randint(1, min(remain, t // 2))
                    parts.append(part)
                    remain -= part
                medium = [x for x in parts if 4 * x >= t]
                if medium:
                    a = medium[0]
                else:
                    a = 0
                    for x in parts:
                        a += x
                        if 4 * a >= t:
                            break
                assert 4 * a >= t and 2 * a <= t
                assert 8 * s <= a
                COUNTS['separator_packing_tests'] += 1


def check_constants():
    for d in range(1, 2001):
        h, m = 1 << d, 1 << (d - 1)
        D = h // (16 * d)
        M = m + d * D
        s = isqrt(d) + (isqrt(d) ** 2 < d)
        assert d * D <= F(h, 16)
        assert M <= F(9 * h, 16)
        assert D + 1 > F(h, 16 * d)
        assert F(5 * h, 2) >= F(17 * h - 16, 7)
        for alpha in [F(1, 8), F(1, 16 * s)]:
            assert (1 - alpha) * F(5 * h, 2) >= h - 2 + 2 * M
            COUNTS['exact_uniform_thresholds'] += 1
        alpha = F(1, 16 * s)
        assert F(34 * h - 32, 15) * (1 - alpha) >= h - 2 + 2 * M
        assert alpha / (1 - alpha) == F(1, 16 * s - 1)
        assert alpha / (1 - alpha) <= F(1, 15 * s)
        if d <= 1000:
            chain = []
            q = d
            while q:
                chain.append(q)
                q //= 2
            for j, v in enumerate(chain):
                assert v >= 2 ** (len(chain) - j - 1)
            numeric = sum(1 / sqrt(v) for v in chain) / 15
            assert numeric <= (2 + sqrt(2)) / 15 + 1e-14
            # Also check the exact rational, slightly stronger budget.
            exact = sum((F(1, 16 * (isqrt(v) + (isqrt(v)**2 < v)) - 1)
                         for v in chain), F(0))
            assert float(exact) < 0.228
            COUNTS['halving_chains'] += 1

    # Analytical monotonicity: q_N decreases once N>4608/49<95.
    assert F(4608, 49) < 95
    for N in (2048, 3072, 4096, 10000):
        log_q = log(2) + F(9, 8) * log(N) - F(49, 4096) * N
        q = exp(float(log_q))
        assert q < 0.25
        bound = 2 * q * (2 - q) / (1 - q) ** 2
        assert bound <= 8 * q
        if N % 6 == 0:
            biclique_log = log(2) + N * log(3) + (N // 6) ** 2 * log(0.75)
            spectral_log = -N * (N - 1) / 64
            assert 8 * q + exp(spectral_log) + exp(biclique_log) < 1
        COUNTS['random_scope_thresholds'] += 1
    assert (2 + sqrt(2)) / 15 < 0.228


def main():
    start = time.time()
    spec = Path(__file__).with_name('Spec.lean')
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_HASH
    for check in [check_small_completion, check_cut_identities, check_all_K6,
                  check_sampled_full_extractions, check_noisy_chains,
                  check_total_error_chains, check_hierarchies_and_separators,
                  check_constants]:
        check()
        print(f'PASS {check.__name__}', flush=True)
    assert COUNTS['K6_colorings'] == 32768
    assert COUNTS['K6_constructed_C4'] == 6224
    assert COUNTS['K6_terminal_core'] == 26544
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_HASH
    print('\nCOUNTS')
    for key, value in sorted(COUNTS.items()):
        print(f'{key}: {value}')
    print(f'\nSpec.lean SHA-256: {SPEC_HASH} (unchanged)')
    print(f'Runtime: {time.time() - start:.3f}s')
    print('All finite checks passed. The robust-core-to-cube implication is NOT claimed.')


if __name__ == '__main__':
    main()
