#!/usr/bin/env python3
"""Independent finite checks for CubeSaturationStructure.md.

Ordinary cube copies are checked with subgraph monomorphism, not induced
subgraph isomorphism. No check asserts the missing structural normal form.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import ceil, comb, exp, gcd, log
from pathlib import Path
import hashlib
import random
import time

import networkx as nx
import numpy as np
from scipy.optimize import linprog

RNG = random.Random(1812026)
SPEC_HASH = "9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b"


def cube(d):
    q = nx.Graph()
    q.add_nodes_from(range(1 << d))
    q.add_edges_from((v, v ^ (1 << j)) for v in q for j in range(d)
                     if v < (v ^ (1 << j)))
    return q


def core_graph(d):
    h, m, t = 1 << d, 1 << (d - 1), d - 1
    a, b = h - d, m - 1
    T = list(range(t))
    A = list(range(t, t + a))
    B = list(range(t + a, t + a + b))
    blue = {tuple(sorted((u, v))) for u in A for v in B}
    g = nx.Graph()
    g.add_nodes_from(range(t + a + b))
    g.add_edges_from(e for e in combinations(g.nodes, 2) if e not in blue)
    return g, T, A, B


def partitions(n):
    """All set partitions, represented as lists of nonempty bit masks."""
    blocks = []

    def rec(v):
        if v == n:
            yield tuple(blocks)
            return
        bit = 1 << v
        for i in range(len(blocks)):
            blocks[i] |= bit
            yield from rec(v + 1)
            blocks[i] ^= bit
        blocks.append(bit)
        yield from rec(v + 1)
        blocks.pop()

    yield from rec(0)


def partition_distance(g):
    n = len(g)
    allmask = (1 << n) - 1
    adj = [sum(1 << u for u in g[v]) for v in range(n)]
    best = [n, n]
    count = 0
    for blocks in partitions(n):
        count += 1
        masks = [0] * n
        for b in blocks:
            for v in range(n):
                if b & (1 << v):
                    masks[v] = b
        within = max((adj[v] ^ (masks[v] ^ (1 << v))).bit_count()
                     for v in range(n))
        between = max((adj[v] ^ (allmask ^ masks[v])).bit_count()
                      for v in range(n))
        best[0] = min(best[0], within)
        best[1] = min(best[1], between)
    return tuple(best), count


def check_core_and_saturation():
    witness_count = 0
    for d in range(2, 9):
        g, T, A, B = core_graph(d)
        q = cube(d)
        h, m = 1 << d, 1 << (d - 1)
        assert len(g) == 3 * m - 2
        assert len(T) < d and len(T) + len(A) == h - 1
        assert len(T) + len(B) < h and len(B) < m
        assert all(u in B or v in B for u, v in nx.complement(g).edges)
        pairs = list(product(A, B))
        if d > 4:
            pairs = RNG.sample(pairs, min(40, len(pairs)))
        for u, v in pairs:
            image = {0: v, 1: u}
            image.update({1 << j: T[j - 1] for j in range(1, d)})
            rest = iter(a for a in A if a != u)
            for x in q:
                if x not in image:
                    image[x] = next(rest)
            assert len(set(image.values())) == h
            added = frozenset((u, v))
            for x, y in q.edges:
                assert g.has_edge(image[x], image[y]) or frozenset(
                    (image[x], image[y])) == added
            witness_count += 1
        if d <= 3:
            assert not nx.algorithms.isomorphism.GraphMatcher(
                g, q).subgraph_is_monomorphic()
            assert not nx.algorithms.isomorphism.GraphMatcher(
                nx.complement(g), q).subgraph_is_monomorphic()

    distances = []
    for d in (2, 3):
        g, _, _, _ = core_graph(d)
        best, count = partition_distance(g)
        assert min(best) == (1 << (d - 1)) - 1
        distances.append((d, len(g), count, best))

    # An independent small vertex-connectivity check, not used by the search.
    cuts = 0
    for d in range(1, 6):
        q = cube(d)
        for k in range(d):
            for removed in combinations(q.nodes, k):
                remaining = set(q.nodes) - set(removed)
                assert nx.is_connected(q.subgraph(remaining))
                cuts += 1

    # All K4 colorings: neither color can be C4-saturated simultaneously.
    es = list(combinations(range(4), 2))
    q = cube(2)
    saturated = []
    free = []
    for mask in range(1 << len(es)):
        g = nx.Graph()
        g.add_nodes_from(range(4))
        g.add_edges_from(e for i, e in enumerate(es) if mask >> i & 1)
        is_free = not nx.algorithms.isomorphism.GraphMatcher(
            g, q).subgraph_is_monomorphic()
        free.append(is_free)
        sat = is_free
        if sat:
            for i, e in enumerate(es):
                if not (mask >> i & 1):
                    g.add_edge(*e)
                    creates = nx.algorithms.isomorphism.GraphMatcher(
                        g, q).subgraph_is_monomorphic()
                    g.remove_edge(*e)
                    if not creates:
                        sat = False
                        break
        saturated.append(sat)
    full = (1 << len(es)) - 1
    assert any(free[x] and free[full ^ x] for x in range(full + 1))
    assert not any(saturated[x] and saturated[full ^ x]
                   for x in range(full + 1))
    assert sum(saturated) == 12
    print(f"Core family: {witness_count} explicit saturation embeddings; "
          "ordinary noncontainment checked in d=2,3.")
    print(f"Exact partition distances (d,N,partitions,(red-within,red-between)): {distances}")
    print(f"Cube vertex connectivity: {cuts} vertex-deletion cases through d=5.")
    print("K4: all 64 colorings checked; 12 one-color C4-saturated graphs, no simultaneous pair.")


def template(t, mask):
    colors = {}
    for k, (i, j) in enumerate((i, j) for i in range(t) for j in range(i, t)):
        colors[i, j] = (mask >> k) & 1
    return colors


def col(colors, i, j):
    return colors[min(i, j), max(i, j)]


def components(t, colors, color):
    left = set(range(t))
    ans = []
    while left:
        root = min(left)
        reached, todo = {root}, [root]
        left.remove(root)
        while todo:
            u = todo.pop()
            new = {v for v in left if col(colors, u, v) == color}
            left -= new
            reached |= new
            todo.extend(new)
        ans.append(tuple(sorted(reached)))
    return ans


def lcm(a, b):
    return a // gcd(a, b) * b


def component_matching(verts, colors, color, capacities):
    edges = [(i, j) for i in verts for j in verts if i <= j
             and col(colors, i, j) == color]
    if not edges:
        return F(0), {}
    mat = [[(int(v == i) + int(v == j)) for i, j in edges] for v in verts]
    result = linprog(-np.ones(len(edges)), A_ub=np.array(mat),
                     b_ub=np.array([float(capacities[v]) for v in verts]),
                     bounds=(0, None), method="highs")
    assert result.success
    denominator = 1
    for v in verts:
        denominator = lcm(denominator, capacities[v].denominator)
    # Basic capacitated graph fractional matchings are half-integral on
    # the common capacity grid. The following checks verify the reconstruction.
    weights = [F(max(0.0, z)).limit_denominator(2 * denominator)
               for z in result.x]
    for r, v in enumerate(verts):
        assert sum(F(mat[r][j]) * weights[j] for j in range(len(edges))) <= capacities[v]
    assert sum(w > 0 for w in weights) <= len(verts)

    # Independently enumerate all half-integral dual covers.
    dual = None
    index = {v: r for r, v in enumerate(verts)}
    for twice in product(range(3), repeat=len(verts)):
        if all(twice[index[i]] + twice[index[j]] >= 2 for i, j in edges):
            cost = sum(capacities[v] * F(twice[r], 2) for r, v in enumerate(verts))
            if dual is None or cost < dual:
                dual = cost
    assert dual is not None and sum(weights) == dual
    return 2 * sum(weights), {e: w for e, w in zip(edges, weights) if w > 0}


def best_matching(t, colors, capacities):
    best = (F(-1), None, None, None)
    for color in range(2):
        for verts in components(t, colors, color):
            mass, weights = component_matching(verts, colors, color, capacities)
            if mass > best[0]:
                best = mass, color, verts, weights
    assert best[0] >= F(2, 3) * sum(capacities)
    return best


def check_matching_lemma():
    count = 0
    samples = []
    for t in range(1, 4):
        for mask in range(1 << (t * (t + 1) // 2)):
            colors = template(t, mask)
            for w in product(range(1, 4), repeat=t):
                capacities = list(map(F, w))
                best = best_matching(t, colors, capacities)
                count += 1
                if RNG.randrange(30) == 0:
                    samples.append((t, colors, capacities, best))
    for mask in range(1 << 10):
        colors = template(4, mask)
        best = best_matching(4, colors, [F(1)] * 4)
        count += 1
        if RNG.randrange(25) == 0:
            samples.append((4, colors, [F(1)] * 4, best))
    for t in (4, 5, 6):
        for _ in range(50):
            colors = template(t, RNG.randrange(1 << (t * (t + 1) // 2)))
            capacities = [F(RNG.randrange(1, 10)) for _ in range(t)]
            best = best_matching(t, colors, capacities)
            count += 1
            samples.append((t, colors, capacities, best))
    print(f"Connected fractional matching: {count} weighted looped templates; "
          "LP primal values checked against exhaustive half-integral dual covers.")
    return samples


def make_walk(colors, color, verts, edge_weights, scale):
    mass = 2 * sum(edge_weights.values())
    assert mass > 0
    k = len(verts)
    q = {e: w / mass for e, w in edge_weights.items()}
    p = {v: F(0) for v in verts}
    copies = Counter()
    for (u, v), w in q.items():
        p[u] += w
        p[v] += w
        z = scale * w
        copies[u, v] += 2 * (z.numerator // z.denominator)

    reached, todo = {verts[0]}, [verts[0]]
    while todo:
        u = todo.pop()
        for v in verts:
            if v not in reached and col(colors, u, v) == color:
                reached.add(v)
                todo.append(v)
                copies[min(u, v), max(u, v)] += 2
    assert reached == set(verts)
    copies = +copies
    length = sum(copies.values())
    occurrences = {v: 0 for v in verts}
    adj = {v: {} for v in verts}
    for (u, v), c in copies.items():
        assert col(colors, u, v) == color
        occurrences[u] += c
        occurrences[v] += c
        adj[u][v] = c
        if v != u:
            adj[v][u] = c
    for v in verts:
        assert occurrences[v] % 2 == 0
        occurrences[v] //= 2
    assert abs(length - scale) <= 2 * k
    assert sum(occurrences.values()) == length
    for v in verts:
        assert abs(occurrences[v] - scale * p[v]) <= 2 * k
        assert abs(F(occurrences[v], length) - p[v]) <= F(8 * k, scale)

    stack = [verts[0]]
    circuit = []
    while stack:
        u = stack[-1]
        if not adj[u]:
            circuit.append(stack.pop())
            continue
        v = next(iter(adj[u]))
        adj[u][v] -= 1
        if not adj[u][v]:
            del adj[u][v]
        if v != u:
            adj[v][u] -= 1
            if not adj[v][u]:
                del adj[v][u]
        stack.append(v)
    walk = list(reversed(circuit))
    assert len(walk) == length + 1 and walk[0] == walk[-1]
    assert Counter(walk[:-1]) == occurrences
    assert all(col(colors, u, v) == color for u, v in zip(walk, walk[1:]))
    return walk[:-1], p


def check_walks_and_capacity(samples):
    walks = []
    for t, colors, capacities, best in samples:
        mass, color, verts, weights = best
        scale = RNG.randrange(4 * t, 40 * t + 1)
        walk, _ = make_walk(colors, color, verts, weights, scale)
        walks.append((t, colors, color, walk))

    # Full algebraic capacity test with the theorem's scale. Actual enormous
    # cubes are not generated; the independently checked Fourier upper bound
    # is substituted exactly as in the proof.
    cases = 0
    for t, colors, capacities, _ in samples[::4]:
        eps = F(1, 2)
        a = [2 * x / sum(capacities) for x in capacities]
        keep = [i for i in range(t) if a[i] >= eps / (2 * t)]
        small_colors = {(i, j): col(colors, keep[i], keep[j])
                        for i in range(len(keep)) for j in range(i, len(keep))}
        small_a = [a[i] for i in keep]
        mass, color, verts, weights = best_matching(len(keep), small_colors, small_a)
        assert mass >= 1 + eps / 3
        eta = eps * eps / (8 * t)
        scale = ceil(16 * t / eta)
        walk, p = make_walk(small_colors, color, verts, weights, scale)
        L = len(walk)
        Lstar = ceil(132 * t * t / (eps * eps))
        assert L <= Lstar
        counts = Counter(walk)
        for v in verts:
            assert small_a[v] - p[v] >= eta
            assert F(counts[v], L) <= small_a[v] - eta / 2
        d0 = (Lstar * Lstar / 2) * log(float(16 * t * Lstar / (eps * eps)))
        residual = L * exp(-2 * ceil(d0) / (L * L))
        assert residual <= float(eta / 2) * (1 + 1e-12)
        for v in verts:
            assert float(F(counts[v], L)) + residual <= float(small_a[v]) + 1e-12
        cases += 1
    print(f"Euler-walk rounding: {len(walks)} exact rational instances; "
          f"{cases} full theorem-scale capacity/error estimates.")
    return walks


def check_fourier():
    cases = 0
    for L in range(2, 41):
        for d in range(1, 129):
            counts = [0] * L
            for k in range(d + 1):
                counts[k % L] += comb(d, k)
            bound = exp(-2 * d / (L * L))
            assert sum(counts) == 1 << d
            for z in counts:
                error = float(abs(F(z, 1 << d) - F(1, L)))
                assert error <= bound * (1 + 1e-12) + 1e-300
            cases += 1
    print(f"Binomial residues: {cases} (d,L) pairs, every residue checked exactly before comparison.")


def check_greedy(walks):
    instances = 0
    for _ in range(240):
        t, colors, color, walk = RNG.choice(walks)
        d = RNG.randrange(1, 7)
        D = RNG.randrange(3)
        q = cube(d)
        labels = {x: walk[x.bit_count() % len(walk)] for x in q}
        need = Counter(labels.values())
        pools = [[] for _ in range(t)]
        hostlabels = []
        for i in range(t):
            for _ in range(need[i] + d * D):
                pools[i].append(len(hostlabels))
                hostlabels.append(i)
        n = len(hostlabels)
        wrong = set()
        for _ in range(D):
            order = list(range(n))
            RNG.shuffle(order)
            for u, v in zip(order[0::2], order[1::2]):
                wrong.add(tuple(sorted((u, v))))
        wrongdeg = Counter()
        for u, v in wrong:
            wrongdeg[u] += 1
            wrongdeg[v] += 1
        assert max(wrongdeg.values(), default=0) <= D

        def actual(u, v):
            assert u != v
            return col(colors, hostlabels[u], hostlabels[v]) ^ (tuple(sorted((u, v))) in wrong)

        order = list(q.nodes)
        RNG.shuffle(order)
        image, used = {}, set()
        for x in order:
            candidates = [v for v in pools[labels[x]] if v not in used
                          and all(actual(v, image[y]) == color for y in q[x] if y in image)]
            assert candidates
            image[x] = candidates[0]
            used.add(candidates[0])
        assert len(used) == 1 << d
        assert all(hostlabels[image[x]] == labels[x] for x in q)
        assert all(actual(image[x], image[y]) == color for x, y in q.edges)
        instances += 1
    print(f"Actual injective greedy embedding: {instances} cube/template cases with incident errors D=0,1,2.")


def check_asymptotic_parameters():
    # Verify finite parameter substitutions only. These are not searches for
    # large-dimensional saturated graphs or simultaneous countercolorings.
    cases = 0
    for a in (0, 1, 4):
        for b in (0, F(1, 10), 1, 3):
            C = F(a) + F(3, 2) + 3 * b + 1
            d = 100
            h, m = 1 << d, 1 << (d - 1)
            N = ceil(C * h)
            D = (F(b) * h / d).__floor__()
            nmin = N - a * h
            assert nmin >= 3 * (m + d * D) - 1
            assert nmin > h + d * D
            # p=1/8 gives 2 sqrt(p)=2^(-1/2).
            assert log(float(C + 1)) - d * log(2) / 2 < -20
            cases += 1
    print(f"One-sided saturation obstruction: {cases} finite first-moment/threshold substitutions.")


def main():
    start = time.monotonic()
    spec = Path(__file__).with_name("Spec.lean")
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_HASH
    check_core_and_saturation()
    samples = check_matching_lemma()
    walks = check_walks_and_capacity(samples)
    check_fourier()
    check_greedy(walks)
    check_asymptotic_parameters()
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == SPEC_HASH
    print("Spec.lean SHA-256 unchanged:", SPEC_HASH)
    print("ALL CHECKS PASSED; no missing normal-form or Ramsey assertion was assumed.")
    print(f"Elapsed seconds: {time.monotonic() - start:.2f}")


if __name__ == "__main__":
    main()
