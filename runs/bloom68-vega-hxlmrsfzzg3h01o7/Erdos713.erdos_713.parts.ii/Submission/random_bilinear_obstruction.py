#!/usr/bin/env python3
"""Finite checks for RandomBilinearObstruction.md; no extremal disproof claimed.

All copy counters are for ordinary, injective, side-preserving subgraphs.
Extra edges are permitted. No external packages are required.
"""
from fractions import Fraction
from itertools import combinations, permutations, product
from math import prod
import random


def gf2_basis(vectors):
    pivots = {}
    for value in vectors:
        x = value
        while x:
            p = x.bit_length() - 1
            if p in pivots:
                x ^= pivots[p]
            else:
                pivots[p] = x
                break
    return tuple(pivots[p] for p in sorted(pivots, reverse=True))


def gf2_rank(vectors):
    return len(gf2_basis(vectors))


def reduce_mod(x, basis):
    for b in basis:
        if x & (1 << (b.bit_length() - 1)):
            x ^= b
    return x


def span(vectors):
    values = {0}
    for v in vectors:
        values |= {x ^ v for x in tuple(values)}
    return frozenset(values)


def all_subspaces(d):
    spaces = {frozenset({0})}
    todo = list(spaces)
    while todo:
        current = todo.pop()
        for x in range(1, 1 << d):
            if x not in current:
                enlarged = current | frozenset(y ^ x for y in current)
                if enlarged not in spaces:
                    spaces.add(enlarged)
                    todo.append(enlarged)
    return tuple(sorted(spaces, key=lambda s: (len(s), tuple(sorted(s)))))


def admissible_kernels(d):
    forbidden = {1 << i for i in range(d)}
    forbidden |= {(1 << i) ^ (1 << j) for i in range(d) for j in range(i)}
    return tuple(k for k in all_subspaces(d) if not (k & forbidden))


def quotient_images(d, kernel):
    basis = gf2_basis(kernel)
    return tuple(reduce_mod(1 << i, basis) for i in range(d))


def tensor(x, y, right_dimension):
    result = 0
    i = 0
    while x:
        if x & 1:
            result ^= y << (i * right_dimension)
        i += 1
        x >>= 1
    return result


def copy_types(left_size, right_size, edges):
    output = []
    for kl, kr in product(admissible_kernels(left_size),
                          admissible_kernels(right_size)):
        xs = quotient_images(left_size, kl)
        ys = quotient_images(right_size, kr)
        columns = [tensor(xs[i], ys[j], right_size) for i, j in edges]
        rho = gf2_rank(columns)
        marker = 1 << (left_size * right_size)
        consistent = gf2_rank([v | marker for v in columns]) == rho
        output.append((kl, kr, gf2_rank(xs), gf2_rank(ys), rho, consistent))
    return output


def P(k, d):
    if k > d:
        return 0
    return prod((1 << d) - (1 << i) for i in range(k))


def expected_by_types(left_size, right_size, edges, d, c):
    return sum((Fraction(P(s, d) * P(t, d), 1 << (c * rho))
                for _, _, s, t, rho, consistent
                in copy_types(left_size, right_size, edges) if consistent), Fraction(0))


def expected_cube(d, c):
    return (Fraction(P(4, d) ** 2 + 2 * P(3, d) * P(4, d), 1 << (12 * c))
            + Fraction(P(3, d) ** 2, 1 << (9 * c)))


def matrix_rows(matrix, d):
    mask = (1 << d) - 1
    return tuple((matrix >> (i * d)) & mask for i in range(d))


def row_form(rows, x):
    result = 0
    for i, row in enumerate(rows):
        if x & (1 << i):
            result ^= row
    return result


def neighbors(matrices, d):
    """b=(1,0,...,0), nonzero vectors as vertices; output right bit masks."""
    rows = [matrix_rows(m, d) for m in matrices]
    result = []
    for x in range(1, 1 << d):
        forms = [row_form(m, x) for m in rows]
        mask = 0
        for y in range(1, 1 << d):
            values = tuple((f & y).bit_count() % 2 for f in forms)
            if values[0] == 1 and not any(values[1:]):
                mask |= 1 << (y - 1)
        result.append(mask)
    return tuple(result)


def direct_copy_count(neigh, right_size, left_size_H, right_size_H, edges):
    count = 0
    for xs in permutations(range(len(neigh)), left_size_H):
        for ys in permutations(range(right_size), right_size_H):
            if all(neigh[xs[i]] & (1 << ys[j]) for i, j in edges):
                count += 1
    return count


def cube_count(neigh):
    """Exact inclusion-exclusion over collisions of the four right vertices.

    For fixed four left vertices, S_j is their triple common neighborhood
    omitting j. Intersections of two or more distinct S_j all equal the
    common neighborhood of all four left vertices. The partition-lattice
    Mobius formula then has only the terms explicitly used below.
    """
    total = 0
    for ids in combinations(range(len(neigh)), 4):
        ns = [neigh[i] for i in ids]
        common = ns[0] & ns[1] & ns[2] & ns[3]
        m = common.bit_count()
        sizes = []
        for j in range(4):
            rest = [ns[i] for i in range(4) if i != j]
            sizes.append((rest[0] & rest[1] & rest[2]).bit_count())
        distinct = (prod(sizes)
                    - m * sum(sizes[i] * sizes[j] for i in range(4) for j in range(i))
                    + 2 * m * sum(sizes) + 3 * m * m - 6 * m)
        assert distinct >= 0
        total += distinct
    return 24 * total


def number_rank_d_matrices(d, r):
    return P(r, d) ** 2 // P(r, r)


def canonical_matrix(d, rank):
    return sum(1 << (i * d + i) for i in range(rank))


def independent_random_vectors(rng, dimension, count):
    result = []
    while len(result) < count:
        x = rng.randrange(1 << dimension)
        if gf2_rank(result + [x]) > len(result):
            result.append(x)
    return result


def binary_field_multiply(a, b, k, irreducible):
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & (1 << k):
            a ^= irreducible
    return result


def extension_field_dot_matrices(k, irreducible):
    """The F_(2^k)^2 dot product, explicitly as k binary 2k-by-2k matrices."""
    d = 2 * k
    output = [0] * k
    for i in range(d):
        for j in range(d):
            if i // k != j // k:
                continue
            value = binary_field_multiply(1 << (i % k), 1 << (j % k), k, irreducible)
            for a in range(k):
                if value & (1 << a):
                    output[a] |= 1 << (i * d + j)
    return tuple(output)


def self_test():
    cube_edges = tuple((i, j) for i in range(4) for j in range(4) if i != j)
    assert len(all_subspaces(4)) == 67
    kernels = admissible_kernels(4)
    assert len(kernels) == 6
    types = copy_types(4, 4, cube_edges)
    surviving = sorted((s, t, rho) for _, _, s, t, rho, ok in types if ok)
    assert surviving == [(3, 3, 9), (3, 4, 12), (4, 3, 12), (4, 4, 12)]
    assert max(Fraction(s + t - 2, rho - 1) for s, t, rho in surviving) == Fraction(6, 11)
    for d in range(1, 8):
        for c in range(1, 6):
            assert expected_by_types(4, 4, cube_edges, d, c) == expected_cube(d, c)
    print('Kernel types: 36 checked, exactly 4 consistent; alteration boundary 6/11.')

    rng = random.Random(7132026)
    fixtures = [tuple([15] * 4), tuple(15 ^ (1 << i) for i in range(4)),
                tuple([31] * 5), tuple([0] * 5)]
    fixtures += [tuple(rng.randrange(32) for _ in range(5)) for _ in range(40)]
    for ns in fixtures:
        right_size = 4 if len(ns) == 4 else 5
        assert cube_count(ns) == direct_copy_count(ns, right_size, 4, 4, cube_edges)
    assert cube_count(fixtures[0]) == 576
    assert cube_count(fixtures[1]) == 24
    assert cube_count(fixtures[2]) == 14400
    print('Ordinary cube counter: 44 fixtures agree with direct injective enumeration.')

    # Exact averaging over all 2^9 scalar bilinear maps at d=3.
    counts_by_rank = {}
    sum_cubes = 0
    matrices_with_cube = 0
    for matrix in range(1 << 9):
        ns = neighbors((matrix,), 3)
        value = cube_count(ns)
        rank = gf2_rank(matrix_rows(matrix, 3))
        counts_by_rank.setdefault(rank, set()).add(value)
        sum_cubes += value
        matrices_with_cube += (value > 0)
    assert Fraction(sum_cubes, 1 << 9) == expected_cube(3, 1)
    assert counts_by_rank == {0: {0}, 1: {576}, 2: {0}, 3: {0}}
    assert matrices_with_cube == 49
    print('All 512 maps at d=3,c=1: E[cubes]=441/8; exactly 49 contain a cube.')

    # GL(d,2) x GL(d,2) acts transitively on scalar matrices of a given rank.
    # Its changes of basis are permutations of our nonzero vertices.
    for d in (3, 4):
        weighted_sum = 0
        total_matrices = 0
        table = []
        for r in range(d + 1):
            multiplicity = number_rank_d_matrices(d, r)
            count = cube_count(neighbors((canonical_matrix(d, r),), d))
            total_matrices += multiplicity
            weighted_sum += multiplicity * count
            table.append((r, multiplicity, count))
        assert total_matrices == 1 << (d * d)
        assert Fraction(weighted_sum, total_matrices) == expected_cube(d, 1)
        if d == 4:
            print('All 65,536 scalar d=4 maps via rank classes:', table)
            print('Exact expected labelled cube count:', Fraction(weighted_sum, total_matrices))

    # Validate the general type formula independently on several ordinary H.
    small_H = [
        (2, 1, ((0, 0), (1, 0))),
        (1, 3, ((0, 0), (0, 1), (0, 2))),
        (2, 2, ((0, 0), (1, 0), (1, 1))),
        (2, 2, tuple(product(range(2), repeat=2))),
        (3, 3, tuple((i, j) for i in range(3) for j in range(3) if i != j)),
        (2, 2, ((0, 0), (1, 1))),
    ]
    for lh, rh, es in small_H:
        total = sum(direct_copy_count(neighbors((m,), 2), 3, lh, rh, es)
                    for m in range(16))
        assert Fraction(total, 16) == expected_by_types(lh, rh, es, 2, 1)
    print('General copy-type formula: 6 additional H checked over all 16 d=2 scalar maps.')

    # Exact edge and edge-pair probabilities, including a genuinely vector-valued map.
    for c in (1, 2):
        possibilities = 16 ** c
        singles = [0] * 9
        pairs = {(i, j): 0 for i in range(9) for j in range(i)}
        for ms in product(range(16), repeat=c):
            ns = neighbors(ms, 2)
            active = [i * 3 + j for i in range(3) for j in range(3)
                      if ns[i] & (1 << j)]
            for i in active:
                singles[i] += 1
            for ii, i in enumerate(active):
                for j in active[:ii]:
                    pairs[i, j] += 1
        assert all(v == possibilities // (2 ** c) for v in singles)
        assert all(v == possibilities // (2 ** (2 * c)) for v in pairs.values())
    print('Pairwise edge independence: complete distributions for (d,c)=(2,1),(2,2).')

    for _ in range(600):
        du, dv = 5, 4
        a = independent_random_vectors(rng, du, rng.randrange(5))
        aa = independent_random_vectors(rng, du, rng.randrange(5))
        b = independent_random_vectors(rng, dv, rng.randrange(5))
        bb = independent_random_vectors(rng, dv, rng.randrange(5))
        s = gf2_rank(a) + gf2_rank(aa) - gf2_rank(a + aa)
        t = gf2_rank(b) + gf2_rank(bb) - gf2_rank(b + bb)
        ab = [tensor(x, y, dv) for x in a for y in b]
        aabb = [tensor(x, y, dv) for x in aa for y in bb]
        intersection_rank = gf2_rank(ab) + gf2_rank(aabb) - gf2_rank(ab + aabb)
        assert intersection_rank == s * t
    for s in range(1, 4):
        for t in range(1, 4):
            assert Fraction(s + t, s * t) >= Fraction(2, 3)
    print('Second-moment identities: 600 tensor intersections and all 9 dimension ratios checked.')

    field_tests = []
    for q in (2, 3, 5, 7, 11, 13):
        vertices = [(x, y) for x in range(q) for y in range(q) if x or y]
        ns = []
        for x, y in vertices:
            ns.append(sum(1 << i for i, (a, b) in enumerate(vertices)
                          if (x * a + y * b) % q == 1))
        assert all(n.bit_count() == q for n in ns)
        assert all((ns[i] & ns[j]).bit_count() <= 1
                   for i in range(len(ns)) for j in range(i))
        assert sum(n.bit_count() for n in ns) == (q * q - 1) * q
        field_tests.append((q, 2 * (q * q - 1), (q * q - 1) * q))
    print('C4-free comparison (field order, vertices, edges):', field_tests)

    # This is a crucial scope test: exceptional deterministic maps beat the
    # random cube threshold while staying in exactly the same binary model.
    structured_tests = []
    for k, polynomial in ((2, 0b111), (3, 0b1011), (4, 0b10011)):
        q, d = 1 << k, 2 * k
        # Verify these small quotients are fields (every nonzero element acts bijectively).
        for a in range(1, q):
            assert {binary_field_multiply(a, b, k, polynomial) for b in range(q)} == set(range(q))
        matrices = extension_field_dot_matrices(k, polynomial)
        ns = neighbors(matrices, d)
        assert len(matrices) == k
        assert all(n.bit_count() == q for n in ns)
        assert all((ns[i] & ns[j]).bit_count() <= 1
                   for i in range(len(ns)) for j in range(i))
        mask = q - 1
        for x in range(1, 1 << d):
            for y in range(1, 1 << d):
                value = (binary_field_multiply(x & mask, y & mask, k, polynomial)
                         ^ binary_field_multiply(x >> k, y >> k, k, polynomial))
                assert bool(ns[x - 1] & (1 << (y - 1))) == (value == 1)
        if k == 2:
            assert cube_count(ns) == 0
        structured_tests.append((d, k, 2 * len(ns), sum(n.bit_count() for n in ns)))
    print('Exceptional binary maps (d,c,vertices,edges), all C4-free:', structured_tests)
    print('PASS. These finite checks do not assert an irrational extremal exponent.')


if __name__ == '__main__':
    self_test()
