#!/usr/bin/env python3
"""Exact checks for IndependentB3Attack.md; no asymptotic conclusion is inferred.

Checks include repeated summands, integer and cyclic B2 sets, every subgraph
of K_{3,3} and K_{4,4}, and two symplectic generalized-quadrangle examples.
"""
from collections import Counter, defaultdict
from itertools import combinations, combinations_with_replacement, permutations, product
import json
from pathlib import Path


def sum_value(xs, modulus=None):
    s = sum(xs)
    return s if modulus is None else s % modulus


def is_br(A, r, modulus=None):
    seen = set()
    for t in combinations_with_replacement(A, r):
        s = sum_value(t, modulus)
        if s in seen:
            return False
        seen.add(s)
    return True


def boolean_certificate(A, modulus=None):
    assert is_br(A, 2, modulus)
    n = len(A)
    pair_sums = {sum_value(t, modulus)
                 for t in combinations_with_replacement(A, 2)}
    r = Counter(sum_value((s, -a), modulus) for s in pair_sums for a in A)
    h = r.copy()
    for a in A:
        h[a] -= n - 1
    assert all(v >= 0 for v in h.values())
    assert all(h[a] == 1 for a in A)
    assert sum(h.values()) == (n**3 - n**2 + 2*n) // 2
    boolean = all(v in (0, 1) for v in h.values())
    assert boolean == is_br(A, 3, modulus)
    if boolean:
        assert {s for s, v in h.items() if v} == set(r)

    lhs = sum(v*(v-1)//2 for v in h.values())
    triples = defaultdict(list)
    for t in combinations_with_replacement(A, 3):
        triples[sum_value(t, modulus)].append(t)
    rhs = 0
    collisions = 0
    for reps in triples.values():
        for t, u in combinations(reps, 2):
            assert set(t).isdisjoint(u)
            rhs += len(set(t))*len(set(u))
            collisions += 1
    assert lhs == rhs
    assert collisions <= lhs <= 9*collisions
    return boolean, lhs


def all_b2_audits():
    out = {}
    for name, modulus, size in [('integer_0_to_12', None, 13)] + [
            (f'cyclic_{m}', m, m) for m in range(3, 14)]:
        count = b3 = nonzero = 0
        for mask in range(1 << size):
            A = [a for a in range(size) if mask >> a & 1]
            if not is_br(A, 2, modulus):
                continue
            ok, defect = boolean_certificate(A, modulus)
            count += 1
            b3 += ok
            nonzero += defect != 0
        out[name] = {'B2_sets': count, 'B3_sets': b3,
                     'positive_defect_sets': nonzero}
    return out


def short_cycle_masks(n):
    masks = set()
    for xs in combinations(range(n), 2):
        for ys in combinations(range(n), 2):
            masks.add(sum(1 << (x*n+y) for x in xs for y in ys))
    for xs in combinations(range(n), 3):
        for yset in combinations(range(n), 3):
            for ys in permutations(yset):
                edges = {(xs[i], ys[i]) for i in range(3)} | {
                    (xs[(i+1) % 3], ys[i]) for i in range(3)}
                assert len(edges) == 6
                masks.add(sum(1 << (x*n+y) for x, y in edges))
    return sorted(masks)


def exhaustive_product_audit(n):
    # The alphabet is B3 because its base-4 digits in a triple sum are <= 3.
    alphabet = [4**i for i in range(n)]
    assert is_br(alphabet, 3)
    radix = 3*max(alphabet)+1
    values = [x+radix*y for x in alphabet for y in alphabet]
    forbidden = short_cycle_masks(n)
    histogram = Counter()
    count = 0
    for mask in range(1 << (n*n)):
        no_short_cycle = not any(mask & f == f for f in forbidden)
        C = [values[i] for i in range(n*n) if mask >> i & 1]
        actual = is_br(C, 3)
        assert actual == no_short_cycle, (n, mask)
        if actual:
            histogram[len(C)] += 1
        count += 1
    return {'graphs_checked': count, 'B3_graphs_by_edge_count': dict(histogram),
            'maximum_edges': max(histogram)}


def normalize(v, q):
    for a in v:
        if a:
            inv = pow(a, -1, q)
            return tuple(inv*b % q for b in v)
    raise ValueError('zero vector')


def symplectic(x, y, q):
    return (x[0]*y[1]-x[1]*y[0]+x[2]*y[3]-x[3]*y[2]) % q


def quadrangle_audit(q):
    # q is prime for these two checks.
    points = sorted({normalize(v, q) for v in product(range(q), repeat=4) if any(v)})
    index = {p: i for i, p in enumerate(points)}
    lines = set()
    for x, y in combinations(points, 2):
        if symplectic(x, y, q):
            continue
        span = {index[normalize(tuple((a*xi+b*yi) % q for xi, yi in zip(x, y)), q)]
                for a, b in product(range(q), repeat=2) if a or b}
        assert len(span) == q+1
        lines.add(tuple(sorted(span)))
    lines = sorted(lines)
    n = q**3+q**2+q+1
    assert len(points) == len(lines) == n
    X = [set() for _ in points]
    Y = [set(line) for line in lines]
    edges = []
    for j, line in enumerate(lines):
        for i in line:
            X[i].add(j)
            edges.append((i, j))
    assert all(len(s) == q+1 for s in X+Y)
    # Every non-backtracking 3-path has nonadjacent endpoints, and those
    # endpoints determine it. This independently excludes both C4 and C6.
    for x in range(n):
        endpoints = Counter()
        for v in X[x]:
            for u in Y[v]-{x}:
                for y in X[u]-{v}:
                    assert y not in X[x]
                    endpoints[y] += 1
        assert all(k == 1 for k in endpoints.values())
    alphabet = [4**i for i in range(n)]
    radix = 3*max(alphabet)+1
    C = [alphabet[i]+radix*alphabet[j] for i, j in edges]
    assert is_br(C, 3)
    return {'points_per_part': n, 'edges': len(edges),
            'degree': q+1, 'integer_multiset_triples_checked':
            len(C)*(len(C)+1)*(len(C)+2)//6}


def main():
    report = {
        'boolean_and_weighted_defect_identity': all_b2_audits(),
        'cartesian_product_characterization': {
            str(n): exhaustive_product_audit(n) for n in (3, 4)},
        'sharp_exponent_examples': {
            str(q): quadrangle_audit(q) for q in (2, 3)},
    }
    destination = Path(__file__).with_name('independent_b3_audit.json')
    destination.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
