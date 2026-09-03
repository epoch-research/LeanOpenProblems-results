#!/usr/bin/env python3
"""Finite checks for CubeEndpointConflictInvestigation.md.

No test or result here asserts the missing full-square-graph estimate or the
linear cube Ramsey bound. All computations use only the Python standard library.
"""
from fractions import Fraction
from itertools import combinations, permutations
from math import comb, exp, factorial, fsum, isclose, lgamma, log, log1p
from pathlib import Path
import hashlib
import random

ROOT = Path(__file__).resolve().parent
SPEC_HASH = "9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b"


def square_edges(a, b, mask):
    out = []
    for x, xp in combinations(range(a), 2):
        for y, yp in combinations(range(b), 2):
            cells = (x * b + y, x * b + yp, xp * b + y, xp * b + yp)
            if all(mask >> z & 1 for z in cells):
                out.append((cells[0], cells[3]))
                out.append((cells[1], cells[2]))
    return out


def contains_c4(n, edges):
    adj = [0] * n
    for x, y in edges:
        adj[x] |= 1 << y
        adj[y] |= 1 << x
    return any((adj[x] & adj[y]).bit_count() >= 2
               for x, y in combinations(range(n), 2))


def permutation_moments(a, b, mask):
    """Check all random-injection identities for one bipartite graph."""
    e = mask.bit_count()
    da = [sum(mask >> (x * b + y) & 1 for y in range(b)) for x in range(a)]
    db = [sum(mask >> (x * b + y) & 1 for x in range(a)) for y in range(b)]
    aux = square_edges(a, b, mask)
    xs = []
    sum_aux = 0
    for pi in permutations(range(b), a):
        labels = [x * b + pi[x] for x in range(a)
                  if mask >> (x * b + pi[x]) & 1]
        selected = set(labels)
        xs.append(len(labels))
        sum_aux += sum(u in selected and v in selected for u, v in aux)
    count = len(xs)
    mu = Fraction(e, b)
    mean = Fraction(sum(xs), count)
    var = Fraction(sum(x * x for x in xs), count) - mu * mu
    assert mean == mu
    assert Fraction(sum_aux, count) == Fraction(len(aux), b * (b - 1))
    degree_sum = sum(x * x for x in da) + sum(y * y for y in db)
    exx = Fraction(e * e - degree_sum + e, b * (b - 1))
    assert Fraction(sum(x * (x - 1) for x in xs), count) == exx
    var_formula = (Fraction(e, b - 1) + Fraction(e * e, b * b * (b - 1))
                   - Fraction(degree_sum, b * (b - 1)))
    assert var == var_formula
    var_bound = Fraction(b, b - 1) * mu * (1 - Fraction(e, a * b))
    assert var <= var_bound
    if e:
        for alpha in [0.0, 0.25, 0.5, 0.75, 1.0]:
            actual = sum(x ** (2 - alpha) for x in xs) / count
            bound = float(mu) ** (2 - alpha) + (1 - alpha) * float(mu) ** (-alpha) * float(var)
            assert actual <= bound + 1e-10
    return e, len(aux), xs, mu, var


def check_permutation_identities():
    count = 0
    for a in range(1, 4):
        for b in range(max(2, a), 5):
            for mask in range(1 << (a * b)):
                permutation_moments(a, b, mask)
                count += 1
    # Additional nontrivial balanced examples with more than three matching labels.
    rng = random.Random(181)
    for a, b in [(4, 4), (4, 5), (5, 5)]:
        for _ in range(64):
            mask = rng.getrandbits(a * b)
            permutation_moments(a, b, mask)
            count += 1
    return count


def check_all_four_by_four_lifts():
    """Q3 on four vertices per part is K4,4 minus a perfect matching.

    Check all 65536 G, comparing that characterization with C4s in all
    endpoint-disjoint four-label restrictions of S(G). Also check (4) exactly
    whenever G is Q3-free, using ex(x,C4) for 0 <= x <= 4.
    """
    b = 4
    ex_c4 = [0, 0, 1, 3, 4]
    row_bits = [15 << (4 * x) for x in range(4)]
    col_bits = [sum(1 << (4 * x + y) for x in range(4)) for y in range(4)]
    templates = []
    for pi in permutations(range(4)):
        label_bits = sum(1 << (4 * x + pi[x]) for x in range(4))
        # Each template entry records the four original cells needed for an
        # auxiliary edge, including the two matching labels themselves.
        pairs = []
        for x, xp in combinations(range(4), 2):
            rect = sum(1 << z for z in
                       [4 * x + pi[x], 4 * x + pi[xp],
                        4 * xp + pi[x], 4 * xp + pi[xp]])
            pairs.append((x, xp, rect))
        templates.append((label_bits, pairs))
    free_count = 0
    for mask in range(1 << 16):
        missing = mask ^ ((1 << 16) - 1)
        direct_q3 = (all((missing & r).bit_count() <= 1 for r in row_bits)
                     and all((missing & c).bit_count() <= 1 for c in col_bits))
        matching_c4 = False
        sum_aux = 0
        sum_ex = 0
        for label_bits, pairs in templates:
            selected_edges = [(x, xp) for x, xp, rect in pairs if mask & rect == rect]
            sum_aux += len(selected_edges)
            x = (mask & label_bits).bit_count()
            sum_ex += ex_c4[x]
            if x == 4 and contains_c4(4, selected_edges):
                matching_c4 = True
        assert matching_c4 == direct_q3
        s = len(square_edges(4, 4, mask))
        assert sum_aux == 2 * s  # 24 permutations / [b(b-1)] = 2
        if not direct_q3:
            free_count += 1
            assert sum_aux <= sum_ex
            e = mask.bit_count()
            if e:
                # A=1/2, B=1/2 dominate ex(x,C4) for 0<=x<=4.
                alpha, A, B = 0.5, 0.5, 0.5
                p = e / 16
                upper = (A * (1 - 1 / b) * b ** alpha * e ** (2 - alpha)
                         + A * (1 - alpha) * b ** (1 + alpha) * e ** (1 - alpha) * (1 - p)
                         + B * (b - 1) * e)
                assert s <= upper + 1e-10
    return free_count


def rook_allowed_edges(a, b):
    cells = list(range(a * b))
    return [(x, y) for x, y in combinations(cells, 2)
            if x // b != y // b and x % b != y % b]


def check_exact_relaxation_small():
    """Exhaust all J on [3]x[3] for H=P3 and H=K3."""
    a = b = 3
    allowed = rook_allowed_edges(a, b)
    assert len(allowed) == 18
    index = {uv: i for i, uv in enumerate(allowed)}
    triples = []
    for pi in permutations(range(b), a):
        labels = [x * b + pi[x] for x in range(a)]
        tri = sum(1 << index[tuple(sorted(uv))] for uv in combinations(labels, 2))
        triples.append(tri)
    # Every allowed edge occurs in (b-2)! = 1 matching restriction here.
    assert sum(t.bit_count() for t in triples) == 18
    assert len(set(bit for t in triples for bit in range(18) if t >> bit & 1)) == 18
    max_p3 = max_k3 = 0
    for mask in range(1 << 18):
        counts = [(mask & t).bit_count() for t in triples]
        if max(counts) <= 1:
            max_p3 = max(max_p3, mask.bit_count())
        if max(counts) <= 2:
            max_k3 = max(max_k3, mask.bit_count())
    assert max_p3 == b * (b - 1) * 1  # ex(3,P3)=1
    assert max_k3 == b * (b - 1) * 2  # ex(3,K3)=2
    return max_p3, max_k3


def check_relaxation_construction():
    """Check the extremizing construction for every graph T on four rows."""
    a = b = 4
    base_pairs = list(combinations(range(a), 2))
    maxima = 0
    full_rook = set(rook_allowed_edges(a, b))
    for mask in range(1 << len(base_pairs)):
        base = {uv for i, uv in enumerate(base_pairs) if mask >> i & 1}
        j_edges = set()
        for x, xp in base:
            for y in range(b):
                for yp in range(b):
                    if y != yp:
                        j_edges.add((x * b + y, xp * b + yp))
        assert j_edges <= full_rook
        assert len(j_edges) == b * (b - 1) * len(base)
        for x, xp in combinations(range(a), 2):
            for y, yp in combinations(range(b), 2):
                diagonal1 = (x * b + y, xp * b + yp)
                diagonal2 = (x * b + yp, xp * b + y)
                assert (diagonal1 in j_edges) == (diagonal2 in j_edges)
        for pi in permutations(range(b), a):
            restricted = {(x, xp) for x, xp in base_pairs
                          if (x * b + pi[x], xp * b + pi[xp]) in j_edges}
            assert restricted == base
        if not contains_c4(a, base):
            maxima = max(maxima, len(j_edges))
        if len(base) < len(base_pairs):
            # All four labels of a nonedge rectangle are present, but its
            # diagonals are absent: paired-diagonal symmetry is not full closure.
            x, xp = next(uv for uv in base_pairs if uv not in base)
            assert (x * b, xp * b + 1) not in j_edges
            assert (x * b + 1, xp * b) not in j_edges
    assert maxima == b * (b - 1) * 4  # ex(4,C4)=4
    return maxima


def check_dense_obstructions():
    # Exact finite square formula and required error-normalization identities.
    for d in range(2, 11):
        m = 1 << (d - 1)
        for C in [1, 2, 4, 8, 64]:
            a, b = m - 1, (2 * C - 1) * m + 1
            N = a + b
            e = a * b
            s = a * (a - 1) * b * (b - 1) // 2
            assert N == C * (1 << d)
            assert a < m
            assert Fraction(s, e * e) == Fraction((a - 1) * (b - 1), 2 * a * b)
            assert Fraction(e, N * m) == Fraction((m - 1) * ((2 * C - 1) * m + 1), 2 * C * m * m)
        for C in [2, 4, 8]:
            x, y = m - 1, (C - 1) * m + 1
            e = 2 * x * y
            s = x * (x - 1) * y * (y - 1)
            assert Fraction(s, e * e) == Fraction((x - 1) * (y - 1), 4 * x * y)
    # Limits evaluated at a large dimension using logarithms of exact integers.
    d = 10000
    m = 1 << (d - 1)
    alpha = 2 / (d + 1)
    for C in [1, 2, 8, 64, 1024]:
        a, b = m - 1, (2 * C - 1) * m + 1
        ratio = 0.5 * (1 - 1 / a) * (1 - 1 / b) * exp(alpha * log(a * b))
        assert abs(ratio - 8) < 0.009
        if C >= 2:
            x, y = m - 1, (C - 1) * m + 1
            ratio_bal = 0.25 * (1 - 1 / x) * (1 - 1 / y) * exp(alpha * log(2 * x * y))
            assert abs(ratio_bal - 4) < 0.005


def probabilistic_lower_log(k, C):
    """Stable version of (11), including k for which 2**k exceeds floats."""
    inv_m = 2.0 ** (-k)
    log_t = log(C) + k * log(2)
    beta_den = k / 2 - inv_m
    log_p = (inv_m * lgamma(k) - (1 - 2 * inv_m) * log_t) / beta_den
    lower_density = 0.5 * (1 - inv_m / C - 2 * inv_m / k) * exp(log_p)
    normalized_aux = lower_density * (1 - inv_m / C) * exp(4 * log_t / (k + 2))
    return log_p, lower_density, normalized_aux


def check_random_alteration_normalization():
    for k in range(2, 101):
        m = 1 << k
        ell = k * m // 2
        assert Fraction(factorial(k - 1), m * factorial(k)) == Fraction(1, 2 * ell)
        for C in [1, 2, 8, 64]:
            t = C * m
            lp = (lgamma(k) - (m - 2) * log(t)) / (ell - 1)
            stable, density, aux_ratio = probabilistic_lower_log(k, C)
            assert lp <= 0
            assert isclose(lp, stable, abs_tol=1e-12)
            assert density > 0 and aux_ratio > 0
    for C in [1, 2, 8, 64, 1024]:
        lp, density, aux_ratio = probabilistic_lower_log(100000, C)
        assert abs(exp(lp) - 0.25) < 0.00004
        assert abs(density - 0.125) < 0.00002
        assert abs(aux_ratio - 2) < 0.0002
    # Generic error obstruction: choose C after K and the leading gap.
    for K in [0.0, 0.5, 1.0, 10.0, 100.0]:
        for T in [0.5, 1.0, 1.5, 1.99]:
            C = int(32 * K / (2 - T)) + 2
            assert T / 16 + 2 * K / C < 1 / 8


def exact_c4_embedding_count_rook(t):
    shared = (t - 1) * (t - 2)
    disjoint = (t - 2) ** 2
    return (2 * t * t * (t - 1) * shared * (shared - 1)
            + t * t * (t - 1) ** 2 * disjoint * (disjoint - 1))


def check_birthday_algebra():
    # Independently count injective C4 homomorphisms for small complete G.
    for t in [3, 4, 5]:
        aux = set(rook_allowed_edges(t, t))
        def adjacent(u, v):
            return tuple(sorted((u, v))) in aux
        actual = 0
        good = 0
        for q in permutations(range(t * t), 4):
            if all(adjacent(q[i], q[(i + 1) % 4]) for i in range(4)):
                actual += 1
                if len({x // t for x in q}) == 4 and len({x % t for x in q}) == 4:
                    good += 1
        assert actual == exact_c4_embedding_count_rook(t)
        falling = 0 if t < 4 else t * (t - 1) * (t - 2) * (t - 3)
        assert good == falling * falling
    # Check the explicit lower denominator / upper numerator bound for k=2
    # when its stated size hypothesis applies.
    for t in range(10, 101):
        k, m = 2, 4
        ordinary = exact_c4_embedding_count_rook(t)
        good = (t * (t - 1) * (t - 2) * (t - 3)) ** 2
        lower_i = exp(2 * m * log(t) - 2 * k * m / t - m * (m - 1) / t ** 2)
        upper_d = exp(2 * m * log(t) - m * (m - 1) / t)
        assert ordinary + 1e-6 >= lower_i
        assert good <= upper_d + 1e-6
        ratio_upper = exp(-m * (m - 1) / t + 2 * k * m / t + m * (m - 1) / t ** 2)
        assert good / ordinary <= ratio_upper + 1e-12
    # Verify the exponential-rate Riemann sum and positivity of gamma_C.
    for C in [2, 4, 8, 64]:
        gamma = 2 * (1 + (C - 1) * log1p(-1 / C))
        assert gamma > 0
        k, m = 16, 1 << 16
        log_norm_d = 2 * fsum(log1p(-j / (C * m)) for j in range(m))
        assert abs(log_norm_d / m + gamma) < 0.00003
        correction_i_per_m = (2 * k / C + 1 / C ** 2) / m
        assert correction_i_per_m < 0.00025


def check_conditional_sufficiency_constants():
    """Only checks: IF the unproved (18) holds, the stated C gives a contradiction."""
    for eps in [Fraction(1, 100), Fraction(1, 10), Fraction(1, 2), Fraction(1), Fraction(3, 2)]:
        for K in [Fraction(0), Fraction(1, 4), Fraction(1), Fraction(10), Fraction(100)]:
            C = max(Fraction(6), 128 * (K + 1) / eps)
            assert (8 * K + Fraction(17, 8)) / C < eps / 16
            for d in range(1, 31):
                h, m = 1 << d, 1 << (d - 1)
                N = (C * h).__ceil__()
                e0 = Fraction(N * (N - 1), 8)
                assert N >= 6 * h
                assert e0 >= 4 * h * h
                alpha = Fraction(2, d + 1)
                # (4 h^2)^alpha = 16, checked in exponent form.
                assert (2 + 2 * d) * alpha == 4
                lower = Fraction((N - 1) ** 2, 8 * N * N) - Fraction(4, N)
                assert lower >= Fraction(1, 8) - Fraction(17, 4 * N)
                err = Fraction(8 * K * m, N - 1) + Fraction(17, 4 * N)
                assert err <= (8 * K + Fraction(17, 8)) / C
                assert err < eps / 16
                upper = (2 - eps) / 16 + Fraction(8 * K * m, N - 1)
                assert upper < lower


def main():
    assert hashlib.sha256((ROOT / "Spec.lean").read_bytes()).hexdigest() == SPEC_HASH
    n = check_permutation_identities()
    print(f"PASS: random-injection identities, exact variance and moment bounds on {n} bipartite graphs")
    qfree = check_all_four_by_four_lifts()
    print(f"PASS: all 65536 four-by-four graphs; exact cube/matching lift; averaged extremal bound on {qfree} Q3-free graphs")
    p3, k3 = check_exact_relaxation_small()
    print(f"PASS: all 262144 generic auxiliaries on [3]x[3]; exact maxima P3={p3}, K3={k3}")
    c4 = check_relaxation_construction()
    print(f"PASS: all 64 four-row constructions; exact C4-free maximum in the construction={c4}; paired diagonals do not imply full closure")
    check_dense_obstructions()
    print("PASS: dense original obstructions, balanced variant and required error normalizations")
    check_random_alteration_normalization()
    print("PASS: self-contained random-alteration coefficient, limiting generic coefficient 2, and controlled-error obstruction")
    check_birthday_algebra()
    print("PASS: exact small cube copy counts, birthday inequalities and exponential-rate normalization")
    check_conditional_sufficiency_constants()
    print("PASS: finite constants in conditional majority-density sufficiency calculation")
    assert hashlib.sha256((ROOT / "Spec.lean").read_bytes()).hexdigest() == SPEC_HASH
    print(f"PASS: Spec.lean unchanged; SHA256={SPEC_HASH}")
    print("No check asserts the missing full-square-graph estimate (18) or the linear Ramsey bound.")


if __name__ == "__main__":
    main()
