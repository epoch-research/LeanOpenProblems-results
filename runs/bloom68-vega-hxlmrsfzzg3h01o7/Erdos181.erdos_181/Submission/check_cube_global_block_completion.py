#!/usr/bin/env python3
"""Exact small audits of the unsuccessful global-cover DRC attempt.

No assertion here is the missing asymptotic inequality. All source labels,
original-vertex disjointness, and prescribed outer edges are retained.
Integer weights u represent vertex weights w=u/3; every partition identity
is homogeneous, so clearing this common denominator is exact.
"""
from functools import lru_cache
from itertools import combinations, permutations
from math import prod
from pathlib import Path
import hashlib

SPEC_HASH = "9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b"


def cube_edges(d):
    return [(x, x ^ (1 << j)) for x in range(1 << d)
            for j in range(d) if not (x >> j) & 1]


def graph(n, edges):
    g = [[False] * n for _ in range(n)]
    for v, w in edges:
        assert v != w
        g[v][w] = g[w][v] = True
    return g


def complement(g):
    return [[i != j and not g[i][j] for j in range(len(g))]
            for i in range(len(g))]


def audit(name, g, k, r):
    n, b, m = len(g), 1 << k, 1 << (r - 1)
    even = [x for x in range(1 << r) if x.bit_count() % 2 == 0]
    odd = [x for x in range(1 << r) if x.bit_count() % 2 == 1]
    even_index = {x: i for i, x in enumerate(even)}
    internal = cube_edges(k)
    omega = [f for f in permutations(range(n), b)
             if all(g[f[a]][f[c]] for a, c in internal)]
    masks = [sum(1 << v for v in f) for f in omega]
    u = [1 + v % 3 for v in range(n)]
    weights = [prod(u[v] for v in f) for f in omega]
    aux = [set() for _ in omega]
    for i, f in enumerate(omega):
        for j, h in enumerate(omega):
            if not masks[i] & masks[j] and all(g[f[a]][h[a]] for a in range(b)):
                aux[i].add(j)
    all_choices = tuple(range(len(omega)))

    @lru_cache(None)
    def packing_weight(choices, length, used=0):
        if length == 0:
            return 1
        if n - used.bit_count() < length * b:
            return 0
        return sum(weights[i] * packing_weight(choices, length - 1, used | masks[i])
                   for i in choices if not used & masks[i])

    def packings(choices, length, used=0, prefix=(), weight=1):
        if length == 0:
            yield prefix, used, weight
            return
        for i in choices:
            if not used & masks[i]:
                yield from packings(choices, length - 1, used | masks[i],
                                    prefix + (i,), weight * weights[i])

    @lru_cache(None)
    def small_cover(edge_masks, available, bound):
        """An actual original-vertex cover, not an auxiliary vertex count."""
        vertices = [v for v in range(n) if available >> v & 1]
        for size in range(min(bound, len(vertices)) + 1):
            for vs in combinations(vertices, size):
                s = sum(1 << v for v in vs)
                if all(s & e for e in edge_masks):
                    return s
        return None

    @lru_cache(None)
    def audit_maximal_cover(edge_masks):
        used, count = 0, 0
        for e in edge_masks:
            if not used & e:
                used |= e
                count += 1
        assert used.bit_count() == b * count
        assert all(e & used for e in edge_masks)
        return True

    def completion(f, families, used):
        order = sorted(range(m), key=lambda i: len(families[i]))
        selected = {}

        def rec(j, occupied):
            if j == m:
                return dict(selected)
            site = order[j]
            for i in families[site]:
                if not occupied & masks[i]:
                    selected[site] = i
                    answer = rec(j + 1, occupied | masks[i])
                    if answer is not None:
                        return answer
                    del selected[site]
            return None

        answer = rec(0, used)
        if answer is not None:
            image = [None] * (b * (1 << r))
            for x, i in zip(even, f):
                image[x*b:(x+1)*b] = omega[i]
            for j, x in enumerate(odd):
                image[x*b:(x+1)*b] = omega[answer[j]]
            assert len(set(image)) == len(image)
            assert all(g[image[a]][image[c]] for a, c in cube_edges(k + r))
        return answer

    total = bad_weight = 0
    packing_count = good_count = completes = conservative = partition_checks = 0
    all_vertices = (1 << n) - 1
    for f, used, weight in packings(all_choices, m):
        packing_count += 1
        available = all_vertices ^ used
        families = []
        for y in odd:
            neighbours = [f[even_index[y ^ (1 << j)]] for j in range(r)]
            options = set(all_choices)
            for i in neighbours:
                options.intersection_update(aux[i])
            options = tuple(sorted(i for i in options if not masks[i] & used))
            # Independently construct the coordinate-specific domains.
            domains = [{v for v in range(n) if available >> v & 1 and
                        all(g[v][omega[i][a]] for i in neighbours)}
                       for a in range(b)]
            direct_options = tuple(i for i, h in enumerate(omega)
                                   if all(h[a] in domains[a] for a in range(b)))
            assert options == direct_options
            families.append(options)
            audit_maximal_cover(tuple(sorted(set(masks[i] for i in options))))
            # Check every deletion in the residual host, with exact weights.
            s = available
            while True:
                lhs = sum(weights[i] for i in options if not masks[i] & s)
                rhs = sum(weights[i] for i, h in enumerate(omega)
                          if all(h[a] in domains[a] and not (s >> h[a] & 1)
                                 for a in range(b)))
                assert lhs == rhs
                partition_checks += 1
                if s == 0:
                    break
                s = (s - 1) & available

        bad = False
        for bits in range(1, 1 << m):
            edges = tuple(sorted({masks[i] for j in range(m) if bits >> j & 1
                                  for i in families[j]}))
            bound = (2*b - 1) * (bits.bit_count() - 1)
            cover = small_cover(edges, available, bound)
            if cover is not None:
                assert cover.bit_count() <= bound
                assert not cover & used
                assert all(cover & e for e in edges)
                bad = True
                break
        answer = completion(f, families, used)
        completes += answer is not None
        conservative += bad and answer is not None
        if not bad:
            good_count += 1
            assert answer is not None  # finite audit of Haxell's application

        common = set(all_choices)
        for i in f:
            common.intersection_update(aux[i])
        root_weight = packing_weight(tuple(sorted(common)), 2)
        total += weight * root_weight
        bad_weight += weight * root_weight * bad

    # Reverse the order of summation: first two globally disjoint test roots,
    # then an integral m-packing in their common auxiliary neighbourhood.
    forward_total = 0
    for roots, _, weight in packings(all_choices, 2):
        a = tuple(sorted(aux[roots[0]] & aux[roots[1]]))
        forward_total += weight * packing_weight(a, m)
    assert total == forward_total
    assert 0 <= bad_weight <= total
    print(f"{name}: k={k}, r={r}; even packings={packing_count}; "
          f"cover-good={good_count}; completable={completes}; "
          f"cover-bad but completable={conservative}; "
          f"T={total}; B={bad_weight}; partitions={partition_checks}")
    return packing_count, partition_checks, total, bad_weight


def main():
    cases = []
    for n in (8, 9):
        cases.append((f"K{n}", graph(n, combinations(range(n), 2)), 1, 2))
    bip = graph(8, [(i, j) for i in range(4) for j in range(4, 8)])
    cube = graph(8, cube_edges(3))
    patterned = graph(8, [(i, j) for i, j in combinations(range(8), 2)
                         if (3*i + j) % 5 <= 2])
    cases += [("K4,4", bip, 1, 2), ("Q3", cube, 1, 2),
              ("complement Q3", complement(cube), 1, 2),
              ("K4,4 singleton blocks", bip, 0, 3),
              ("Q3 singleton blocks", cube, 0, 3),
              ("patterned", patterned, 0, 3),
              ("complement patterned", complement(patterned), 0, 3)]
    results = [audit(*case) for case in cases]
    assert any(t > b for _, _, t, b in results)
    assert any(t == b > 0 for _, _, t, b in results)
    spec = Path(__file__).with_name("Spec.lean")
    digest = hashlib.sha256(spec.read_bytes()).hexdigest()
    assert digest == SPEC_HASH
    print(f"TOTAL: {len(cases)} hosts/blockings; "
          f"{sum(x[0] for x in results)} integral even packings; "
          f"{sum(x[1] for x in results)} coordinate-domain partition checks.")
    print("Spec.lean SHA-256:", digest)
    print("PASS: exact DRC summation, actual cover certificates, and all lifted edges.")
    print("NOT PROVED: B_R+B_B < T_R+T_B at N >= C*2^d; no uniform embedding.")


if __name__ == "__main__":
    main()
