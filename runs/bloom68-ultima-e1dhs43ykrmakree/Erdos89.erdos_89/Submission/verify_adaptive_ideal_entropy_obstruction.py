#!/usr/bin/env python3
"""Finite checks for adaptive_ideal_entropy_obstruction.md.

Gaussian arithmetic and combinatorial counts are exact integers. Entropies use
floating logarithms; they check identities, not the asymptotic theorems.
Requires numpy. Does not invoke or modify Lean.
"""
from __future__ import annotations

import itertools
import math
import random
from collections import Counter, defaultdict
from fractions import Fraction

import numpy as np

G = tuple[int, int]
ZERO: G = (0, 0)
ONE: G = (1, 0)


def add(a: G, b: G) -> G:
    return a[0] + b[0], a[1] + b[1]


def sub(a: G, b: G) -> G:
    return a[0] - b[0], a[1] - b[1]


def mul(a: G, b: G) -> G:
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def conj(a: G) -> G:
    return a[0], -a[1]


def norm(a: G) -> int:
    return a[0] ** 2 + a[1] ** 2


def power(a: G, k: int) -> G:
    z = ONE
    for _ in range(k):
        z = mul(z, a)
    return z


def exact_div(a: G, b: G) -> G:
    m = norm(b)
    t = mul(a, conj(b))
    assert t[0] % m == 0 and t[1] % m == 0
    return t[0] // m, t[1] // m


def divides(b: G, a: G) -> bool:
    m = norm(b)
    t = mul(a, conj(b))
    return t[0] % m == 0 and t[1] % m == 0


def quotient_remainder(a: G, b: G) -> tuple[G, G]:
    m = norm(b)
    assert m > 0
    t = mul(a, conj(b))
    # Half-up rounding is translation equivariant, unlike bankers' rounding.
    q = ((2 * t[0] + m) // (2 * m), (2 * t[1] + m) // (2 * m))
    r = sub(a, mul(q, b))
    assert 2 * norm(r) <= m
    return q, r


def rem(a: G, b: G) -> G:
    return quotient_remainder(a, b)[1]


def bezout_unit(a: G, b: G) -> tuple[G, G]:
    r0, r1 = a, b
    s0, s1 = ONE, ZERO
    t0, t1 = ZERO, ONE
    while r1 != ZERO:
        q, r = quotient_remainder(r0, r1)
        r0, r1 = r1, r
        s0, s1 = s1, sub(s0, mul(q, s1))
        t0, t1 = t1, sub(t0, mul(q, t1))
    assert norm(r0) == 1
    u = conj(r0)
    s, t = mul(u, s0), mul(u, t0)
    assert add(mul(s, a), mul(t, b)) == ONE
    return s, t


def crt(a: G, ma: G, b: G, mb: G) -> G:
    s, _ = bezout_unit(ma, mb)
    z = add(a, mul(ma, rem(mul(sub(b, a), s), mb)))
    z = rem(z, mul(ma, mb))
    assert divides(ma, sub(z, a)) and divides(mb, sub(z, b))
    return z


def val_int(d: int, p: int) -> int:
    assert d > 0
    k = 0
    while d % p == 0:
        d //= p
        k += 1
    return k


def val_gauss(z: G, pi: G) -> int:
    assert z != ZERO
    k = 0
    while divides(pi, z):
        z = exact_div(z, pi)
        k += 1
    return k


def actual_alphabet(points: list[G], pi: G) -> set[int]:
    p = norm(pi)
    values = set()
    for x, y in itertools.combinations(points, 2):
        z = sub(x, y)
        v = val_int(norm(z), p)
        assert v == val_gauss(z, pi) + val_gauss(z, conj(pi))
        values.add(v)
    return values


def groups(points: list[G], beta: G) -> list[list[G]]:
    out: dict[G, list[G]] = defaultdict(list)
    for z in points:
        out[rem(z, beta)].append(z)
    return list(out.values())


def adaptive_cover(points: list[G], pi: G) -> tuple[set[int], list[int]]:
    """Keep actual normalized fibers, not just collision totals."""
    assert len(points) == len(set(points)) and len(points) >= 2
    p = norm(pi)
    V = actual_alphabet(points, pi)
    nodes = [points]
    counts = [1]
    entropy = 0.0
    for depth in range(max(V) + 1):
        new_nodes = []
        for A in nodes:
            local_V = actual_alphabet(A, pi)
            assert all(v + depth in V for v in local_V)
            children = groups(A, pi)
            beta = pi
            if depth not in V:
                if len(children) != 1:
                    beta = conj(pi)
                    children = groups(A, beta)
                assert len(children) == 1, "row-or-column consequence failed"
            assert len(children) <= p
            probs = [len(child) / len(A) for child in children]
            entropy += (len(A) / len(points)) * -sum(t * math.log(t) for t in probs)
            for child in children:
                anchor = child[0]
                B = [exact_div(sub(z, anchor), beta) for z in child]
                assert len(B) == len(set(B))
                new_nodes.append(B)
        nodes = new_nodes
        counts.append(len(nodes))
        allowed_so_far = sum(v <= depth for v in V)
        assert len(nodes) <= p ** allowed_so_far
    assert all(len(A) == 1 for A in nodes)
    assert len(nodes) == len(points) <= p ** len(V)
    assert abs(entropy - math.log(len(points))) < 1e-10
    return V, counts


def correlated_crt_set(pi: G, V: list[int]) -> list[G]:
    assert all(V[j + 1] - V[j] >= 2 for j in range(len(V) - 1))
    p = norm(pi)
    t = len(V)
    a = list(range(t))
    b = [V[j] - j for j in range(t)]
    ma, mb = power(pi, t), power(conj(pi), b[-1] + 1)
    out = []
    for word in itertools.product(range(p), repeat=t):
        u, v = ZERO, ZERO
        for j, d in enumerate(word):
            # A permutation of the current digit, depending on the prefix.
            sigma_d = ((j % (p - 1) + 1) * d + sum(word[:j]) + j) % p
            u = add(u, mul((d, 0), power(pi, a[j])))
            v = add(v, mul((sigma_d, 0), power(conj(pi), b[j])))
        out.append(crt(u, ma, v, mb))
    assert len(set(out)) == p ** t
    assert actual_alphabet(out, pi) == set(V)
    if t >= 2:
        # Ensure these tests are not merely a real-line realization.
        x = out[0]
        assert any(
            sub(y, x)[0] * sub(z, x)[1] != sub(y, x)[1] * sub(z, x)[0]
            for y, z in itertools.combinations(out[1:], 2)
        )
    return out


def test_adaptive() -> None:
    pi = (2, 1)
    small_grid = list(itertools.product(range(3), repeat=2))
    checked = 0
    for mask in range(1 << len(small_grid)):
        P = [z for j, z in enumerate(small_grid) if mask >> j & 1]
        if len(P) >= 2:
            adaptive_cover(P, pi)
            checked += 1
    print(f"Exact adaptive cover: all {checked} subsets of the 3x3 grid with >=2 points.")
    rng = random.Random(4512025)
    for split_pi in [(2, 1), (3, 2), (4, 1)]:
        for _ in range(60):
            m = rng.randrange(2, 26)
            P = rng.sample(list(itertools.product(range(-17, 18), repeat=2)), m)
            adaptive_cover(P, split_pi)
    print("Exact adaptive cover: 180 randomized actual sets at split primes 5,13,17.")
    for split_pi, V in [
        ((2, 1), [0, 2, 4]),
        ((2, 1), [0, 3, 6]),
        ((2, 1), [1, 4, 7]),
        ((3, 2), [0, 2]),
    ]:
        P = correlated_crt_set(split_pi, V)
        actual, counts = adaptive_cover(P, split_pi)
        p = norm(split_pi)
        assert counts == [p ** sum(v < k for v in V) for k in range(max(V) + 2)]
        print(f"Sharp correlated CRT set: p={p}, V={sorted(actual)}, n={len(P)}, counts={counts}")
    grid = list(itertools.product(range(12), repeat=2))
    V, counts = adaptive_cover(grid, pi)
    assert 0 in V and 1 in V and 2 in V and 3 in V
    print(f"Actual 12x12 low-D grid has both valuation parities: V={sorted(V)}, counts={counts}")
    for h in [2, 4, 11, 30]:
        P = [(0, 0), (1, 0), (2**h, 0), (2**h + 1, 0)]
        first = groups(P, (1, 1))
        assert sorted(map(len, first)) == [2, 2]
        assert all(val_gauss(sub(A[0], A[1]), (1, 1)) == 2 * h for A in first)
        # Gaussian primitive, because difference 1 occurs.
        assert sub(P[1], P[0]) == ONE
    print("Primitive fixed-cardinality example: arbitrarily many zero-entropy unary refinements checked.")


def grid_radial_counts(L: int) -> np.ndarray:
    v = np.arange(L, dtype=np.int64)
    sign_v = np.where(v == 0, 1, 2)
    r = np.zeros(2 * (L - 1) ** 2 + 1, dtype=np.int64)
    for u in range(L):
        d = u * u + v * v
        # d has no repeats in this row, so indexed addition is exact.
        r[d] += (1 if u == 0 else 2) * sign_v * (L - u) * (L - v)
    n = L * L
    assert int(r[0]) == n
    r[0] = 0
    assert int(r.sum()) == n * (n - 1)
    return r


def full_rep_counts(T: int) -> np.ndarray:
    r2 = np.zeros(T + 1, dtype=np.int64)
    for u in range(math.isqrt(T) + 1):
        v = np.arange(math.isqrt(T - u * u) + 1, dtype=np.int64)
        r2[u * u + v * v] += (1 if u == 0 else 2) * np.where(v == 0, 1, 2)
    r2[0] = 0
    assert np.all(r2 % 4 == 0)
    return r2


def factor_r2(d: int) -> int:
    result = 4
    p = 2
    while p * p <= d:
        k = 0
        while d % p == 0:
            d //= p
            k += 1
        if p % 4 == 3 and k % 2:
            return 0
        if p % 4 == 1:
            result *= k + 1
        p += 1
    if d > 1:
        if d % 4 == 3:
            return 0
        if d % 4 == 1:
            result *= 2
    return result


def entropy(p: np.ndarray, alpha: float) -> float:
    if alpha == 0:
        return math.log(len(p))
    if alpha == 1:
        return -float(np.dot(p, np.log(p)))
    return math.log(float(np.sum(p**alpha))) / (1 - alpha)


def point_difference_entropy(L: int) -> float:
    n = L * L
    M = n * (n - 1)
    s = math.fsum((1 if u == 0 else 2) * (L - u) * math.log(L - u) for u in range(L))
    return math.log(M) - (2 * n * s - n * math.log(n)) / M


def test_grid_exact() -> None:
    for L in range(2, 9):
        r = grid_radial_counts(L)
        P = list(itertools.product(range(L), repeat=2))
        brute = Counter(norm(sub(x, y)) for x in P for y in P if x != y)
        assert {d: int(r[d]) for d in np.flatnonzero(r)} == dict(brute)
        zd = Counter(sub(x, y) for x in P for y in P if x != y)
        probs = np.array(list(zd.values()), dtype=float) / (len(P) * (len(P) - 1))
        assert abs(entropy(probs, 1) - point_difference_entropy(L)) < 1e-11
    print("Exact grid autocorrelation and radial counts checked against all endpoint pairs for L=2,...,8.")

    rng = random.Random(1324)
    for L in [8, 16, 32, 64, 128, 256]:
        n = L * L
        M = n * (n - 1)
        r = grid_radial_counts(L)
        r2 = full_rep_counts(len(r) - 1)
        for d in rng.sample(range(1, len(r)), min(180, len(r) - 1)):
            assert int(r2[d]) == factor_r2(d)
        assert np.all(r <= n * r2)
        inner = min(n // 4, len(r) - 1)
        assert np.all(4 * r[1:inner + 1] >= n * r2[1:inner + 1])
        mask = r > 0
        rr = r[mask].astype(float)
        p = rr / M
        H1 = entropy(p, 1)
        HZ = point_difference_entropy(L)
        Elogrep = float(np.dot(p, np.log(r2[mask].astype(float))))
        cond_KL = Elogrep - (HZ - H1)
        total_KL = math.log(int(r2.sum())) - HZ
        norm_KL = float(np.dot(p, np.log(p * int(r2.sum()) / r2[mask])))
        assert cond_KL >= -1e-10
        assert cond_KL <= total_KL + 1e-10
        assert abs(total_KL - norm_KL - cond_KL) < 1e-10
        assert total_KL <= math.log(int(r2.sum()) / (n - 1)) + 1e-10
        # Finite Jensen/capacity inequality used in the uniformization bound.
        D = len(p)
        Hjoint_uniform_colors = math.log(D) + float(np.mean(np.log(rr)))
        moment_half = float(np.sum(np.sqrt(r2[r2 > 0].astype(float) / 4)))
        jensen_bound = math.log(D) + math.log(4 * n) + 2 * math.log(moment_half / D)
        assert Hjoint_uniform_colors <= jensen_bound + 1e-10
    print("Representation comparisons, conditional-orientation KL chain rule, and Jensen inequality checked through L=256.")


def test_uniformization() -> None:
    for L in range(2, 7):
        P = list(itertools.product(range(L), repeat=2))
        n = len(P)
        M = n * (n - 1)
        r = grid_radial_counts(L)
        D = int(np.count_nonzero(r))
        mx = [Fraction(0) for _ in P]
        my = [Fraction(0) for _ in P]
        colors = defaultdict(Fraction)
        pairs = []
        for a, x in enumerate(P):
            for b, y in enumerate(P):
                if a == b:
                    continue
                d = norm(sub(x, y))
                w = Fraction(1, D * int(r[d]))
                pairs.append((a, b, w))
                mx[a] += w
                my[b] += w
                colors[d] += w
        assert sum(mx) == sum(my) == 1
        assert all(w == Fraction(1, D) for w in colors.values())
        HX = -math.fsum(float(w) * math.log(float(w)) for w in mx)
        HY = -math.fsum(float(w) * math.log(float(w)) for w in my)
        HXY = -math.fsum(float(w) * math.log(float(w)) for _, _, w in pairs)
        I = math.fsum(float(w) * math.log(float(w / (mx[a] * my[b]))) for a, b, w in pairs)
        rr = r[r > 0].astype(float)
        reverse = math.log(M) - math.log(D) - float(np.mean(np.log(rr)))
        cost = 2 * math.log(n) - HXY
        assert abs(cost - ((math.log(n) - HX) + (math.log(n) - HY) + I)) < 1e-10
        assert abs(cost - (math.log(n / (n - 1)) + reverse)) < 1e-10
        assert abs(HXY - (math.log(D) + float(np.mean(np.log(rr))))) < 1e-10
    print("Uniform-color endpoint laws: exact rational class masses and entropy-cost equality checked for L=2,...,6.")


def entropy_table() -> None:
    print("\nActual square-grid data (natural logarithms; not an asymptotic proof):")
    print(" L          n          D       H0-H1   reverseKL       Phi0       Phi1       Phi2")
    for L in [8, 16, 32, 64, 128, 256, 512, 1024]:
        n = L * L
        M = n * (n - 1)
        r = grid_radial_counts(L)
        rr = r[r > 0].astype(float)
        p = rr / M
        alphas = [0, 0.25, 0.5, 0.75, 1, 1.5, 2, 3]
        HH = [entropy(p, a) for a in alphas]
        assert all(a >= b - 1e-10 for a, b in zip(HH, HH[1:]))
        H0, H1, H2 = entropy(p, 0), entropy(p, 1), entropy(p, 2)
        forward = float(np.dot(p, np.log(p * len(p))))
        reverse = math.log(M) - math.log(len(p)) - float(np.mean(np.log(rr)))
        assert abs(forward - (H0 - H1)) < 1e-10
        assert reverse >= -1e-10
        derivative_zero = H0 + float(np.mean(np.log(p)))
        assert abs(derivative_zero + reverse) < 1e-10
        H_infinity = -math.log(float(np.max(p)))
        assert H_infinity <= H2 + 1e-10
        phi = [math.exp(2 * (math.log(n) - h)) for h in [H0, H1, H2]]
        print(f"{L:4d} {n:10d} {len(p):10d} {H0-H1:11.6f} {reverse:11.6f}"
              f" {phi[0]:10.4f} {phi[1]:10.4f} {phi[2]:10.4f}")
    print("\nPredicted logarithmic exponents 2*c_alpha:")
    for a in [0, 0.25, 0.5, 0.75, 1, 1.5, 2, 3]:
        c = math.log(2) if a == 1 else math.expm1((a - 1) * math.log(2)) / (a - 1)
        assert a == 0 or c > 0.5
        print(f"alpha={a:4g}: 2*c_alpha={2*c:.9f}")
    assert 1.5 - math.sqrt(2) > 0
    print(f"Uniformization cost coefficient (proved lower bound): {1.5-math.sqrt(2):.9f}")


def main() -> None:
    test_adaptive()
    test_grid_exact()
    test_uniformization()
    entropy_table()
    print("\nALL FINITE CHECKS PASSED. No claim that these checks prove the asymptotics or (C0).")


if __name__ == "__main__":
    main()
