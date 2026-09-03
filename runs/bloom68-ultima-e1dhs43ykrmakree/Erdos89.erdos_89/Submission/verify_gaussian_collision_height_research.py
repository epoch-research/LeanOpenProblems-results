#!/usr/bin/env python3
"""Exact checks of the proved constructions, not a search or an asymptotic proof.

No test below asserts the proposed adaptive support-drift lemma.
Only Python's standard library is used.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations
from math import factorial, gcd, isqrt, prod


def compositions(n, m):
    if m == 1:
        yield (n,)
    else:
        for j in range(n + 1):
            for tail in compositions(n - j, m - 1):
                yield (j,) + tail


def check_minimum_collision_mass():
    tests = 0
    for n in range(1, 9):
        for m in range(1, 9):
            a, r = divmod(n, m)
            predicted = m * a * (a - 1) + 2 * a * r
            actual = min(sum(t * (t - 1) for t in c)
                         for c in compositions(n, m))
            assert actual == predicted
            if n <= 2 * m and m < n:
                assert predicted == 2 * (n - m)
            tests += 1
    print(f"Balanced occupancy collision formula: {tests} exact minima checked")


def norm(z):
    return z[0] * z[0] + z[1] * z[1]


def sub(z, w):
    return z[0] - w[0], z[1] - w[1]


def mul(z, w):
    return z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0]


def div_exact(z, w):
    m = norm(w)
    a = z[0] * w[0] + z[1] * w[1]
    b = z[1] * w[0] - z[0] * w[1]
    assert a % m == 0 and b % m == 0
    return a // m, b // m


def gaussian_gcd(z, w):
    while w != (0, 0):
        m = norm(w)
        a = z[0] * w[0] + z[1] * w[1]
        b = z[1] * w[0] - z[0] * w[1]
        # Nearest-integer division, with a deterministic tie convention.
        q = ((2 * a + m) // (2 * m), (2 * b + m) // (2 * m))
        z, w = w, sub(z, mul(q, w))
    return z


def normalize(P):
    P = tuple(P)
    assert len(P) >= 2
    a = P[0]
    g = (0, 0)
    for p in P[1:]:
        g = gaussian_gcd(g, sub(p, a))
    assert g != (0, 0)
    Q = tuple(div_exact(sub(p, a), g) for p in P)
    return Q, g


def residue(z, beta):
    a, b = beta
    m = norm(beta)
    return (a * z[0] + b * z[1]) % m, (a * z[1] - b * z[0]) % m


def fibers(P, beta):
    out = defaultdict(list)
    for p in P:
        out[residue(p, beta)].append(p)
    return tuple(tuple(q) for q in out.values())


def ideal_generators_below(n):
    # Exactly one generator of each nonzero ideal, modulo the four units.
    h = isqrt(n - 1)
    return tuple((a, b) for a in range(1, h + 1)
                 for b in range(h + 1) if 1 < a * a + b * b < n)


def distance_counter(P):
    out = Counter()
    for p, q in combinations(P, 2):
        out[norm(sub(p, q))] += 2
    assert 0 not in out
    return out


def matching_size(rows):
    matched = {}

    def augment(i, seen):
        for d in rows[i]:
            if d in seen:
                continue
            seen.add(d)
            if d not in matched or augment(matched[d], seen):
                matched[d] = i
                return True
        return False

    answer = sum(augment(i, set()) for i in range(len(rows)))
    assert len(matched) == answer
    assert len(set(matched.values())) == answer
    assert all(d in rows[i] for d, i in matched.items())
    # Independently certify maximality by a vertex cover of the same size.
    reached_left = set(range(len(rows))) - set(matched.values())
    reached_right = set()
    stack = list(reached_left)
    while stack:
        i = stack.pop()
        for d in rows[i]:
            if matched.get(d) == i or d in reached_right:
                continue
            reached_right.add(d)
            assert d in matched, "An augmenting path would contradict maximality"
            j = matched[d]
            if j not in reached_left:
                reached_left.add(j)
                stack.append(j)
    cover_left = set(range(len(rows))) - reached_left
    assert len(cover_left) + len(reached_right) == answer
    assert all(i in cover_left or d in reached_right
               for i, row in enumerate(rows) for d in row)
    return answer


def check_translated_grids(L, r):
    k = L * L
    n = r * k
    T = factorial(n)
    h = 2 * (L - 1) ** 2
    assert T > 100 * r * L * L
    A = tuple((x, y) for x in range(L) for y in range(L))
    P = tuple((x + j * T, y) for j in range(r) for x, y in A)
    _, g = normalize(P)
    assert norm(g) == 1
    all_distances = distance_counter(P)
    macro = {j * j * T * T for j in range(1, r)}
    for j in range(1, r):
        assert all_distances[j * j * T * T] == 2 * (r - j) * k
    # Pinned cross-block distances are injective for every nonzero block.
    pinned = {norm(p) for p in P if p[0] >= T}
    assert len(pinned) == (r - 1) * k
    assert len(all_distances) >= n - k

    betas = ideal_generators_below(n)
    rows = []
    norm_rows = defaultdict(set)
    large_count = 0
    for beta in betas:
        m = norm(beta)
        assert T % m == 0
        F = fibers(P, beta)
        row = set()
        collision_mass = 0
        for q in F:
            collision_mass += len(q) * (len(q) - 1)
            row.update(distance_counter(q))
        a, rem = divmod(n, m)
        assert collision_mass >= m * a * (a - 1) + 2 * a * rem
        if m > h:
            large_count += 1
            assert len(F) == k and all(len(q) == r for q in F)
            assert collision_mass == n * (r - 1)
            assert row == macro
            for q in F:
                normalized, gq = normalize(q)
                assert norm(gq) == T * T
                assert len(distance_counter(normalized)) == r - 1
                assert set(distance_counter(normalized)) == {j * j for j in range(1, r)}
        rows.append(row)
        norm_rows[m].update(row)

    small_ideal_rows = sum(norm(b) <= h for b in betas)
    small_norm_rows = len({norm(b) for b in betas if norm(b) <= h})
    nu_ideal = matching_size(rows)
    nu_norm = matching_size(tuple(norm_rows.values()))
    assert nu_ideal <= small_ideal_rows + r - 1
    assert nu_norm <= small_norm_rows + r - 1
    if r == 4:
        near_rows = [rows[i] for i, b in enumerate(betas) if 2 * norm(b) >= n]
        assert near_rows and all(row == macro for row in near_rows)
        assert matching_size(near_rows) <= 3
    if r == k:
        assert nu_ideal <= 5 * isqrt(n)
        assert nu_norm <= 3 * isqrt(n)
    print(f"Translated grids L={L}, r={r}, n={n}: D={len(all_distances)}, "
          f"all proper ideal rows={len(rows)}, large rows={large_count}, "
          f"matching ideals/norms={nu_ideal}/{nu_norm}; exact fibers and gcds passed")
    return P


def is_prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))


def split_primes_above(n, count):
    out = []
    p = n + 1
    while len(out) < count:
        if p % 4 == 1 and is_prime(p):
            out.append(p)
        p += 1
    return out


def crt(residues, moduli):
    M = prod(moduli)
    return sum(a * (M // m) * pow(M // m, -1, m)
               for a, m in zip(residues, moduli)) % M


def crt_primitive_set(n, H):
    edges = tuple(combinations(range(n), 2))
    primes = split_primes_above(n, len(edges))
    p_for = dict(zip(edges, primes))
    moduli = [p ** H for p in primes]
    original = []
    for v in range(n):
        residues = [0 if v in e else v + 1 for e in edges]
        original.append(crt(residues, moduli))
    g = 0
    for x in original[1:]:
        g = gcd(g, x - original[0])
    assert g > 0
    P = tuple((x - original[0]) // g for x in original)
    assert len(set(P)) == n
    assert gcd(*P) == 1
    for (i, j), p in p_for.items():
        assert g % p
        assert (P[i] - P[j]) % (p ** H) == 0
        divisible = [(u, v) for u, v in edges if (P[u] - P[v]) % p == 0]
        assert divisible == [(i, j)]
    return P, p_for


def r2_of_square(x):
    # Exact standard formula, factored only for intentionally small examples.
    x = abs(x)
    assert x > 0
    result = 4
    d = 2
    while d * d <= x:
        exponent = 0
        while x % d == 0:
            x //= d
            exponent += 1
        if d % 4 == 1:
            result *= 2 * exponent + 1
        d += 1
    if x > 1 and x % 4 == 1:
        result *= 3
    return result


def check_crt(n, H, evaluate_weights=False):
    P, p_for = crt_primitive_set(n, H)
    subset_count = 0
    exact_weights = 0
    for k in range(3, n + 1):
        for ids in combinations(range(n), k):
            g = 0
            for j in ids[1:]:
                g = gcd(g, P[j] - P[ids[0]])
            assert g > 0
            for i, j in combinations(ids, 2):
                p = p_for[i, j]
                assert g % p
                assert ((P[i] - P[j]) // g) % (p ** H) == 0
            if evaluate_weights:
                W = sum((Fraction(2, r2_of_square((P[i] - P[j]) // g))
                         for i, j in combinations(ids, 2)), Fraction())
                assert W <= Fraction(k * (k - 1), 4 * (2 * H + 1))
                exact_weights += 1
            subset_count += 1
    # For beta equal to an actual difference, exactly its two ordered endpoints
    # collide: hence J_beta = 2/r_2(1) = 1/2, with no factorization needed.
    witnesses = 0
    for i, j in combinations(range(n), 2):
        beta = abs(P[i] - P[j])
        collisions = [(u, v) for u, v in combinations(range(n), 2)
                      if (P[u] - P[v]) % beta == 0]
        assert collisions == [(i, j)]
        witnesses += 1
    if H >= n * n:
        assert Fraction(n * (n - 1), 4 * (2 * H + 1)) < Fraction(1, 2)
    D = len({(P[i] - P[j]) ** 2 for i, j in combinations(range(n), 2)})
    assert D == n * (n - 1) // 2
    print(f"CRT n={n}, H={H}: primitive, {subset_count} normalized subsets, "
          f"{exact_weights} exact reciprocal sums, {witnesses} J=1/2 witnesses; "
          f"D={D}, coordinate bits <= {max(abs(x).bit_length() for x in P)}")
    return tuple((x, 0) for x in P)


def check_point_tree(P):
    # Build one particular proper normalized ideal tree, using 1+i.
    # This checks only normalization and the entropy budget, NOT the missing lemma.
    root_n = len(P)
    product_identity = Fraction(1)
    internal = 0
    leaves = 0
    stack = [P]
    while stack:
        q = stack.pop()
        n = len(q)
        if n == 1:
            leaves += 1
            continue
        original_distances = distance_counter(q)
        q, common_gcd = normalize(q)
        normalized_distances = distance_counter(q)
        assert {norm(common_gcd) * d: count for d, count in normalized_distances.items()} == original_distances
        children = fibers(q, (1, 1))
        assert len(children) == 2
        assert sum(map(len, children)) == n
        assert all(0 < len(c) < n for c in children)
        phi = Fraction(n * n, len(normalized_distances) ** 2)
        theta = [Fraction(len(c), n) for c in children]
        child_phi = []
        for c in children:
            dc = distance_counter(c)
            assert set(dc).issubset(normalized_distances)
            child_phi.append(Fraction(len(c) ** 2, len(dc) ** 2) if len(c) >= 2 else Fraction(1))
        assert sum(t * f for t, f in zip(theta, child_phi)) >= phi * sum(t ** 3 for t in theta)
        assert 1 - sum(t ** 3 for t in theta) <= 2 * (1 - sum(t ** 2 for t in theta))
        # exp(root_n * weighted entropy) at this node.
        product_identity *= Fraction(n ** n, prod(len(c) ** len(c) for c in children))
        internal += 1
        stack.extend(children)
    assert leaves == root_n
    assert internal == root_n - 1
    assert product_identity == root_n ** root_n
    print(f"Normalized point tree n={root_n}: {internal} proper splits; "
          "entropy telescoping checked as an exact integer product")


def main():
    check_minimum_collision_mass()
    tree_sets = []
    for L, r in ((2, 4), (3, 4), (4, 4), (3, 9), (4, 16)):
        P = check_translated_grids(L, r)
        if len(P) <= 81:
            tree_sets.append(P)
    for n, H, exact in ((3, 1, True), (3, 2, True), (4, 1, True),
                        (3, 9, False), (5, 25, False), (7, 49, False)):
        tree_sets.append(check_crt(n, H, exact))
    for P in tree_sets:
        check_point_tree(P)
    print("PASS: all asserted finite checks. No conjectural support-drift inequality was tested or assumed.")


if __name__ == '__main__':
    main()
