#!/usr/bin/env python3
"""Finite checks for CubeDensityInvestigation.md; no edits to Spec.lean.

The asymptotic statements in the report have mathematical proofs. These checks
verify finite instances and certificates, not the open Ramsey conjecture.
"""
import hashlib
import itertools
import math
import random
from pathlib import Path

SPEC_HASH = "9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b"
assert hashlib.sha256(Path("Submission/Spec.lean").read_bytes()).hexdigest() == SPEC_HASH


def partitions(total, lower=1):
    if total == 0:
        yield ()
    for a in range(lower, total + 1):
        for tail in partitions(total - a, a):
            yield (a,) + tail


def balanced_union(parts, m):
    reachable = {0: ()}
    for i, a in enumerate(parts):
        reachable.update({s + a: inds + (i,) for s, inds in list(reachable.items())})
    N = sum(parts)
    return next((inds for s, inds in reachable.items() if m <= s <= N - m), None)


partition_checks = 0
for N in range(1, 31):
    all_parts = list(partitions(N))
    for m in range(1, (N + 2) // 3 + 1):
        extremal = -1
        for parts in all_parts:
            has_biclique = balanced_union(parts, m) is not None
            criterion = max(parts) <= N - m
            assert has_biclique == criterion, (N, m, parts)
            if not criterion:
                e = math.comb(N, 2) - sum(math.comb(a, 2) for a in parts)
                extremal = max(extremal, e)
            partition_checks += 1
        expected = math.comb(N, 2) - math.comb(N - m + 1, 2)
        assert extremal == expected
print(f"PASS: {partition_checks} integer-partition/bin-packing checks and exact extremal counts")

# An independent ordinary (noninduced) subgraph check in small dimensions.
import networkx as nx
monomorphism_checks = 0
for n in (1, 2, 3):
    m = 1 << (n - 1)
    Q = nx.Graph()
    Q.add_nodes_from(range(2 * m))
    Q.add_edges_from((x, x ^ (1 << i)) for x in range(2 * m) for i in range(n))
    for N in range(max(2 * m, 3 * m - 2), max(2 * m, 3 * m - 2) + 3):
        for parts in partitions(N):
            G = nx.complete_multipartite_graph(*parts)
            actual = nx.algorithms.isomorphism.GraphMatcher(G, Q).subgraph_is_monomorphic()
            assert actual == (max(parts) <= N - m), (n, N, parts)
            monomorphism_checks += 1
print(f"PASS: {monomorphism_checks} independent noninduced graph-copy checks")

for n in range(1, 21):
    m = 1 << (n - 1)
    root = math.isqrt(2 * m * m)
    N = 2 * m + root + (root * root != 2 * m * m)
    extremal = math.comb(N, 2) - math.comb(N - m + 1, 2)
    assert 2 * extremal < math.comb(N, 2)
    N0 = 3 * m - 2
    red_e = math.comb(N0, 2) - math.comb(2 * m - 1, 2)
    if n >= 2:
        assert 2 * red_e >= math.comb(N0, 2)
print("PASS: sharp multipartite density constant and restricted Ramsey construction arithmetic")

# Random finite tests of the robust partition-coloring embedding algorithm.
rng = random.Random(181)
robust_checks = 0
for n in range(1, 5):
    h, m = 1 << n, 1 << (n - 1)
    for D in range(3):
        r = m + n * D
        N = 3 * r - 1
        for trial in range(100):
            cuts = sorted(rng.sample(range(1, N), rng.randrange(N)))
            bounds = [0] + cuts + [N]
            blocks = [set(range(a, b)) for a, b in zip(bounds, bounds[1:])]
            part_of = {v: i for i, block in enumerate(blocks) for v in block}
            red = [[u != v and part_of[u] != part_of[v] for v in range(N)] for u in range(N)]
            edges = list(itertools.combinations(range(N), 2))
            rng.shuffle(edges)
            error_deg = [0] * N
            for u, v in edges:
                if error_deg[u] < D and error_deg[v] < D and rng.random() < 0.2:
                    red[u][v] = red[v][u] = not red[u][v]
                    error_deg[u] += 1
                    error_deg[v] += 1
            assert max(error_deg, default=0) <= D
            large = next((b for b in blocks if len(b) >= h + n * D), None)
            if large is not None:
                pools, color_red = [large, large], False
            else:
                inds = balanced_union(tuple(map(len, blocks)), r)
                assert inds is not None
                A = set().union(*(blocks[i] for i in inds))
                pools, color_red = [A, set(range(N)) - A], True
            image = {}
            for x in range(h):
                prior = [image[x ^ (1 << i)] for i in range(n) if x ^ (1 << i) in image]
                unused = pools[x.bit_count() % 2] - set(image.values())
                choices = [v for v in unused if all(red[u][v] == color_red for u in prior)]
                assert choices, (n, D, trial, x)
                image[x] = min(choices)
            assert len(set(image.values())) == h
            assert all(red[image[x]][image[x ^ (1 << i)]] == color_red
                       for x in range(h) for i in range(n))
            robust_checks += 1
print(f"PASS: {robust_checks} robust-partition greedy embeddings")

# Extended Hamming code: one even codeword in every odd vertex's neighborhood.
for k in range(1, 5):
    n = 1 << k
    def syndrome(x):
        answer = 0
        for i in range(n):
            if x >> i & 1:
                answer ^= i
        return answer
    code = {x for x in range(1 << n) if x.bit_count() % 2 == 0 and syndrome(x) == 0}
    assert len(code) == (1 << (n - 1)) // n
    assert all(sum((y ^ (1 << i)) in code for i in range(n)) == 1
               for y in range(1 << n) if y.bit_count() % 2)
print("PASS: Hamming-code Hall-failure certificates for dimensions 2, 4, 8, 16")

# Tensor injectivity need not descend.
p3_edges = {frozenset((0, 1)), frozenset((1, 2))}
cycle = [(0, 1), (1, 0), (2, 1), (1, 2)]
assert len(set(cycle)) == 4
assert all(all(frozenset((cycle[i][j], cycle[(i + 1) % 4][j])) in p3_edges
               for j in (0, 1)) for i in range(4))
print("PASS: Q_2 embeds in P_3 tensor P_3 although it cannot embed in P_3")

# Explicit three-collision quotient of Q_15: structural certificate, not a
# brute-force search for Q_14. Far endpoints and absence of mixed squares are
# exactly the hypotheses of the lifting proof in the report.
n = 15
h = 1 << n
A = (1 << 5) - 1
B = A << 5
C = A << 10
pairs = [(0, A), (C, B | C), (A | B, A | B | C)]
endpoints = [x for pair in pairs for x in pair]
assert min((x ^ y).bit_count() for x, y in itertools.combinations(endpoints, 2)) >= 5
for i in range(n):
    for bit in (0, 1):
        assert any((u >> i & 1) == bit == (v >> i & 1) for u, v in pairs)
representatives = {v: u for u, v in pairs}
def q(x):
    return representatives.get(x, x)
adj = {q(x): set() for x in range(h)}
for x in range(h):
    for i in range(n):
        y = x ^ (1 << i)
        assert q(x) != q(y)
        adj[q(x)].add(q(y))
assert len(adj) == h - 3
assert sum(map(len, adj.values())) // 2 == n * h // 2
for u, v in pairs:
    for i in range(n):
        for j in range(n):
            a, b = q(u ^ (1 << i)), q(v ^ (1 << j))
            assert adj[a] & adj[b] == {q(u)}
print("PASS: explicit Q_15 quotient has only 3 collision pairs; all mixed-square and halfcube-blocking certificates hold")

# General codimension k certificates with logarithmically many far-apart pairs.
for n, k, even_only in [(48, 1, False), (48, 2, True), (64, 3, True)]:
    r = math.ceil(4 ** k * (k + 2) * math.log(2 * n))
    for attempt in range(100):
        endpoints = [rng.getrandbits(n - int(even_only)) for _ in range(2 * r)]
        if even_only:
            endpoints = [x | ((x.bit_count() % 2) << (n - 1)) for x in endpoints]
            assert all(x.bit_count() % 2 == 0 for x in endpoints)
        if min((x ^ y).bit_count() for x, y in itertools.combinations(endpoints, 2)) >= 5:
            break
    else:
        raise AssertionError("No distance certificate found")
    pairs = list(zip(endpoints[::2], endpoints[1::2]))
    for coords in itertools.combinations(range(n), k):
        patterns = set()
        for u, v in pairs:
            if all((u ^ v) >> i & 1 == 0 for i in coords):
                patterns.add(sum(((u >> i) & 1) << j for j, i in enumerate(coords)))
                if len(patterns) == 1 << k:
                    break
        assert len(patterns) == 1 << k, (n, k, coords)
    print(f"PASS: codimension {k}, dimension {n}, {r} pairs: distance and every-subcube collision certificates (bipartite={even_only})")

# Cube-free graphs dominating the scalar half-density Sidorenko lower bound.
for C in (1, 2, 10, 100):
    n = max(5, math.ceil(math.log2(8 * (C + 1))))
    h, m = 1 << n, 1 << (n - 1)
    N = C * h
    a, b = m - 1, N - m + 1
    log_hom = math.log(2) + m * (math.log(a) + math.log(b))
    log_sid_half = h * math.log(N) - (n * h / 2) * math.log(2)
    assert log_hom > log_sid_half
print("PASS: scalar homomorphism bound obstruction for several constants")

assert hashlib.sha256(Path("Submission/Spec.lean").read_bytes()).hexdigest() == SPEC_HASH
print("PASS: Spec.lean unchanged")
