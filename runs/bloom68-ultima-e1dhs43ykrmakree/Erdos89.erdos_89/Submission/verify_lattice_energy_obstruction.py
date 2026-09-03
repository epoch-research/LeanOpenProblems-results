#!/usr/bin/env python3
"""Exact finite checks for lattice_energy_obstruction.md.

This is not a numerical search for point-set counterexamples. The asymptotic
relaxation obstruction is proved in the accompanying note using Wirsing and
Landau--Ramanujan. These tests check its finite identities and PSD failure.
"""

from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations
from math import factorial, gcd, isqrt, log
from random import Random


def add(z, w):
    return z[0] + w[0], z[1] + w[1]


def sub(z, w):
    return z[0] - w[0], z[1] - w[1]


def mul(z, w):
    return z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0]


def conj(z):
    return z[0], -z[1]


def norm(z):
    return z[0] * z[0] + z[1] * z[1]


def quotient(z, w):
    u, q = mul(z, conj(w)), norm(w)
    assert q > 0
    return F(u[0], q), F(u[1], q)


def divides(w, z):
    q = norm(w)
    u = mul(z, conj(w))
    return u[0] % q == 0 and u[1] % q == 0


def exact_quotient(z, w):
    q = quotient(z, w)
    assert q[0].denominator == q[1].denominator == 1
    return int(q[0]), int(q[1])


def gaussian_gcd(z, w):
    while w != (0, 0):
        den = norm(w)
        u = mul(z, conj(w))
        q = tuple((2 * a + den) // (2 * den) for a in u)
        rem = sub(z, mul(q, w))
        assert norm(rem) < den
        z, w = w, rem
    return z


def autocorrelation(P):
    return Counter(sub(p, q) for p in P for q in P)


def radial(A):
    r = Counter()
    for z, value in A.items():
        if z != (0, 0) and value:
            r[norm(z)] += value
    return r


def invariants(P):
    A = autocorrelation(P)
    r = radial(A)
    return len(P), len(r), sum(v * v for v in r.values())


def check_gcd(P):
    assert len(P) >= 2
    alpha = (0, 0)
    for p in P:
        alpha = gaussian_gcd(alpha, sub(p, P[0]))
    gd = 0
    for p, q in combinations(P, 2):
        gd = gcd(gd, norm(sub(p, q)))
    assert gd == norm(alpha) > 0, (P, gd, alpha)
    Q = [exact_quotient(sub(p, P[0]), alpha) for p in P]
    assert invariants(P) == invariants(Q)
    reduced_gcd = 0
    for p, q in combinations(Q, 2):
        reduced_gcd = gcd(reduced_gcd, norm(sub(p, q)))
    assert reduced_gcd == 1


def check_residue_identities(P):
    A = autocorrelation(P)
    r = radial(A)
    n = len(P)
    for beta in [(1, 1), (2, 1), (3, 2), (3, 0), (4, 3)]:
        q = norm(beta)
        cells = Counter(tuple(a % q for a in mul(z, conj(beta))) for z in P)
        lhs = sum(value for z, value in A.items() if z != (0, 0) and divides(beta, z))
        rhs = sum(k * (k - 1) for k in cells.values())
        assert lhs == rhs
        assert q * lhs >= n * n - q * n
    for p in [5, 13, 17, 29]:
        root = next(t for t in range(p) if (t * t + 1) % p == 0)
        cells = Counter(((x + root * y) % p, (x - root * y) % p) for x, y in P)
        rows, cols = Counter(), Counter()
        for (u, v), k in cells.items():
            rows[u] += k
            cols[v] += k
        lhs = sum(k for d, k in r.items() if d % p == 0)
        rhs = sum(k * k for k in rows.values()) + sum(k * k for k in cols.values())
        rhs -= sum(k * k for k in cells.values()) + n
        assert lhs == rhs
    for p in [3, 7, 11, 19]:
        cells = Counter((x % p, y % p) for x, y in P)
        lhs = sum(k for d, k in r.items() if d % p == 0)
        assert lhs == sum(k * k for k in cells.values()) - n
    M, D, E = n * (n - 1), len(r), sum(k * k for k in r.values())
    assert sum(r.values()) == M
    for modulus in [2, 3, 5, 12]:
        sizes, masses = Counter(), Counter()
        for d, k in r.items():
            sizes[d % modulus] += 1
            masses[d % modulus] += k
        rhs = sum(F(masses[j] ** 2 * D, M * M * sizes[j]) for j in sizes)
        discrepancy = sum(
            (F(masses[j], M) - F(sizes[j], D)) ** 2 / F(sizes[j], D)
            for j in sizes
        )
        assert rhs == 1 + discrepancy
        assert F(E * D, M * M) >= rhs


def check_rotations(P):
    A = autocorrelation(P)
    r = radial(A)
    shells = defaultdict(list)
    for z in A:
        if z != (0, 0):
            shells[norm(z)].append(z)
    rotations = {quotient(w, z) for shell in shells.values() for z in shell for w in shell}
    total = 0
    for rho in rotations:
        assert norm(rho) == 1
        translations = Counter(sub(q, mul(rho, p)) for p in P for q in P)
        motion_energy = sum(k * (k - 1) for k in translations.values())
        correlation_energy = 0
        for z, value in A.items():
            if z == (0, 0):
                continue
            w = mul(rho, z)
            if w[0].denominator == w[1].denominator == 1:
                correlation_energy += value * A.get((int(w[0]), int(w[1])), 0)
        assert motion_energy == correlation_energy
        total += motion_energy
    assert total == sum(k * k for k in r.values())


ADJUST_PRIMES = [5, 13, 17, 29, 37, 41, 53, 61, 73, 89, 97, 101, 109, 113, 137]


def is_prime(p):
    return p >= 2 and all(p % k for k in range(2, isqrt(p) + 1))


def build_clipping(X):
    assert X >= 137
    orbits = defaultdict(list)
    # Each nonzero quarter-turn orbit has a unique representative x>0,y>=0.
    for x in range(1, isqrt(X) + 1):
        for y in range(isqrt(X - x * x) + 1):
            orbits[x * x + y * y].append((x, y))
    T = int(log(X) ** (7 / 8))
    assert T >= 2
    b = {d: min(len(reps), T) for d, reps in orbits.items()}
    B0 = sum(b.values())
    h = (B0 - 14) % 16
    for p in ADJUST_PRIMES[:h]:
        assert is_prime(p) and p % 4 == 1 and b[p] == 2
        b[p] -= 1
    B = sum(b.values())
    n = B // 2 + 1
    assert B == B0 - h == 2 * (n - 1)
    assert B % 16 == 14 and n % 8 == 0
    A = {(0, 0): n}
    for d, k in b.items():
        assert 1 <= k <= min(T, len(orbits[d]))
        for x, y in sorted(orbits[d])[:k]:
            for z in [(x, y), (-y, x), (-x, -y), (y, -x)]:
                assert z not in A
                A[z] = n // 8
    r = radial(A)
    assert set(r) == set(orbits)
    assert len(A) == 4 * B + 1
    assert sum(A.values()) == n * n
    assert sum(r.values()) == n * (n - 1)
    assert max(norm(z) for z in A) <= X
    for z, value in A.items():
        assert A.get((-z[1], z[0]), 0) == value
        assert A.get((-z[0], -z[1]), 0) == value
        if z != (0, 0):
            assert value == n // 8
    for d, k in r.items():
        assert k == n // 2 * b[d] and k % 2 == 0
        assert 8 * k <= n * (4 * len(orbits[d]))
    E = sum(k * k for k in r.values())
    assert 4 * E == n * n * sum(k * k for k in b.values())
    assert 2 * E <= n * n * (n - 1) * T
    return n, T, b, A, r, orbits


def check_negative_witness(j):
    a = 3**j
    X = (24 * a) ** 2
    n, T, b, A, r, orbits = build_clipping(X)
    assert T >= 3
    for k in range(1, 25):
        d = (k * a) ** 2
        assert len(orbits[d]) <= 3
        assert b[d] == len(orbits[d])
        assert A.get((k * a, 0), 0) == n // 8
    for k in range(25, 512):
        assert A.get((k * a, 0), 0) == 0
    N = 512
    v = [1 if k % 32 < 16 else -1 for k in range(N)]
    q = sum(v[s] * v[t] * A.get(((s - t) * a, 0), 0) for s in range(N) for t in range(N))
    assert q == -25 * n
    end_terms = [sum(v[s % 32] * v[(s + k) % 32] for s in range(N - k, N)) for k in range(1, 25)]
    assert end_terms == [-k if k <= 16 else 3 * k - 64 for k in range(1, 25)]
    assert sum(end_terms) == -156
    print(f"PSD obstruction j={j}, X={X}, n={n}: quadratic form / n = {F(q,n)} (exact)")
    assert q + N == -25 * n + 512 < 0
    print(f"  Primitive lift: exact quadratic form = {q + N}")


def check_colored_graph():
    n, T, b, A, r, orbits = build_clipping(256)
    labels = [d for d in sorted(b) for _ in range(b[d])]
    assert len(labels) == 2 * (n - 1)
    counts = Counter()
    degrees = defaultdict(Counter)
    seen = set()
    block = 0
    m = n - 1
    for t in range(m):
        matching = [(n - 1, t)] + [((t + k) % m, (t - k) % m) for k in range(1, n // 2)]
        assert len(matching) == n // 2
        assert len({z for edge in matching for z in edge}) == n
        for edges in [matching[:n // 4], matching[n // 4:]]:
            d = labels[block]
            block += 1
            for u, v in edges:
                edge = tuple(sorted((u, v)))
                assert u != v and edge not in seen
                seen.add(edge)
                counts[d] += 2
                degrees[d][u] += 1
                degrees[d][v] += 1
    assert block == len(labels)
    assert len(seen) == n * (n - 1) // 2
    assert counts == r
    for d in degrees:
        assert max(degrees[d].values()) <= b[d] <= len(orbits[d])
    print(f"Colored K_n realization: n={n}, D={len(r)}, all counts and pinned capacities checked")


def check_primitive_extension():
    n0, T, b, A, r, orbits = build_clipping(256)
    n = n0 + 1
    K = factorial(n)
    s = (n0 - 1).bit_length()
    assert 2 * s <= n
    gammas = [(1, K * j) for j in range(1, s + 1)]
    for gamma in gammas:
        assert norm(gaussian_gcd(gamma, conj(gamma))) == 1
    for g, h in combinations(gammas, 2):
        assert gcd(norm(g), norm(h)) == 1
    products = [(1, 0)]
    dstar = 1
    for gamma in gammas:
        dstar *= norm(gamma)
        products = [mul(z, choice) for z in products for choice in [gamma, conj(gamma)]]
    assert len(set(products)) == 2**s
    assert all(norm(z) == dstar and z[0] % K == 1 and z[1] % K == 0 for z in products)
    units = [(1, 0), (0, 1), (-1, 0), (0, -1)]
    representations = {mul(u, z) for u in units for z in products}
    assert len(representations) == 4 * 2**s
    zs = products[:n0]
    Aprime = {(0, 0): n}
    for z, value in A.items():
        if z != (0, 0):
            Aprime[(K * z[0], K * z[1])] = value
    for z in zs:
        assert z not in Aprime and (-z[0], -z[1]) not in Aprime
        Aprime[z] = Aprime[(-z[0], -z[1])] = 1
    rp = radial(Aprime)
    assert sum(Aprime.values()) == n * n
    assert sum(rp.values()) == n * (n - 1)
    assert len(rp) == len(r) + 1 and rp[dstar] == 2 * n0
    assert sum(k * k for k in rp.values()) == sum(k * k for k in r.values()) + 4 * n0 * n0
    assert gcd(K * K, dstar) == 1
    gd = 0
    for d, value in rp.items():
        gd = gcd(gd, d)
        assert value % 2 == 0
    assert gd == 1
    for z, value in Aprime.items():
        assert Aprime.get((-z[0], -z[1]), 0) == value
        if z != (0, 0):
            assert 8 * value <= n
    assert 8 * rp[dstar] <= n * len(representations)
    for d in r:
        assert rp[K * K * d] == r[d]
    endpoints = [(1, 0)] + [sub((1, 0), z) for z in zs]
    assert len(set(endpoints)) == n
    betas = [(x, y) for x in range(1, isqrt(n - 1) + 1)
             for y in range(isqrt(n - 1 - x * x) + 1)]
    betas.append((K, 0))
    for beta in betas:
        q = norm(beta)
        assert divides(beta, (K, 0))
        lhs = sum(value for z, value in Aprime.items() if z != (0, 0) and divides(beta, z))
        assert q * lhs >= n * n - q * n
        assert lhs == (n * (n - 1) if q == 1 else n0 * (n0 - 1))
        def key(z):
            w = mul(z, conj(beta))
            return w[0] % q, w[1] % q
        actual_periodization = Counter()
        for z, value in Aprime.items():
            actual_periodization[key(z)] += value
        expected = Counter()
        expected[key((0, 0))] += n0 * n0 + 1
        expected[key((1, 0))] += n0
        expected[key((-1, 0))] += n0
        assert actual_periodization == expected
        residue_counts = Counter(key(z) for z in endpoints)
        wanted_counts = Counter()
        wanted_counts[key((0, 0))] += n0
        wanted_counts[key((1, 0))] += 1
        assert residue_counts == wanted_counts
    # Outside the tested q<n range the global lower bound is nonpositive.
    assert all(F(n * n, q) - n <= 0 for q in range(n, 2 * n))
    # On any distinct K-scaled test locations, only the diagonal changes.
    for k in range(-511, 512):
        assert Aprime.get((K * k, 0), 0) == A.get((k, 0), 0) + (1 if k == 0 else 0)
    print(f"Primitive extension n={n}: gcd=1, energy/mass formulas, all {len(betas)-1} ideal representatives with norm<n,")
    print("  and full periodizations (including modulo K=n!) agree with one actual endpoint residue set")



def main():
    small = [(x, y) for x in range(-2, 3) for y in range(-2, 3)]
    exhaustive = 0
    for P in combinations(small, 3):
        check_gcd(list(P))
        exhaustive += 1
    print(f"Gaussian gcd lemma: {exhaustive} exhaustive small triples checked")
    rng = Random(481927)
    samples = []
    for _ in range(100):
        k = rng.randrange(2, 10)
        P = set()
        while len(P) < k:
            P.add((rng.randrange(-20, 21), rng.randrange(-20, 21)))
        P = sorted(P)
        samples.append(P)
        check_gcd(P)
        check_residue_identities(P)
        alpha = (10**30 + 3, 10**31 + 1)
        shift = (10**80, -(10**90))
        Q = [add(shift, mul(alpha, z)) for z in P]
        check_gcd(Q)
    print("Gcd, residue, and support-discrepancy identities: 100 further sets checked; huge-coordinate gcd checks included")
    for P in samples[:12] + [[(0, 0), (1, 0)], [(x, y) for x in range(3) for y in range(3)]]:
        check_rotations(P)
    print("Rational rotation identity: 14 exact checks passed")
    for X in [256, 5184, 46656, 131072]:
        n, T, b, A, r, orbits = build_clipping(X)
        print(f"Clipping construction X={X}: n={n}, T={T}, D={len(r)}, all finite identities passed")
    check_colored_graph()
    check_primitive_extension()
    check_negative_witness(1)
    check_negative_witness(2)
    # An anchor-only gcd would incorrectly give 5 instead of 1 here.
    P = [(0, 0), (2, 1), (2, -1)]
    assert gcd(norm(P[1]), norm(P[2])) == 5
    check_gcd(P)
    print("All verification checks passed. No actual point-set counterexample is claimed.")


if __name__ == "__main__":
    main()
