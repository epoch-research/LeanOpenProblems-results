#!/usr/bin/env python3
"""Exact sanity checks for support_sensitive_motion_research.md.

No computation here proves the proposed reverse support inequality RS.
The finite-field examples are not real planar examples and do not have an
absolute GK tail. Python's integer arithmetic is used for all assertions;
random sampling and printed ratios do not enter the exact checks.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations
from math import factorial, gcd, isqrt, log
from random import Random


def norm(z):
    return z[0] * z[0] + z[1] * z[1]


def add(z, w):
    return z[0] + w[0], z[1] + w[1]


def sub(z, w):
    return z[0] - w[0], z[1] - w[1]


def mul(z, w):
    return z[0] * w[0] - z[1] * w[1], z[0] * w[1] + z[1] * w[0]


def conj(z):
    return z[0], -z[1]


def rational_complex(a, b, c):
    assert c != 0
    if c < 0:
        a, b, c = -a, -b, -c
    d = gcd(gcd(abs(a), abs(b)), c)
    return a // d, b // d, c // d


def ratio(z, w):
    a, b = mul(z, conj(w))
    return rational_complex(a, b, norm(w))


def rot_mul(u, v):
    a, b = mul(u[:2], v[:2])
    return rational_complex(a, b, u[2] * v[2])


def rot_inv(u):
    return u[0], -u[1], u[2]


def angle_difference(u, v, base=(1, 0)):
    a = u[0] * v[2] - v[0] * u[2]
    b = u[1] * v[2] - v[1] * u[2]
    a, b = mul((a, b), base)
    return rational_complex(a, b, u[2] * v[2])


def affine_mul(g, h):
    """Exact group law using Fraction translations."""
    u, t = g
    v, s = h
    a, b, c = u
    us = (Fraction(a, c) * s[0] - Fraction(b, c) * s[1],
          Fraction(b, c) * s[0] + Fraction(a, c) * s[1])
    return rot_mul(u, v), add(t, us)


def affine_inv(g):
    u, t = g
    v = rot_inv(u)
    a, b, c = v
    return v, (-Fraction(a, c) * t[0] + Fraction(b, c) * t[1],
               -Fraction(b, c) * t[0] - Fraction(a, c) * t[1])


UNITS = {(1, 0, 1), (-1, 0, 1), (0, 1, 1), (0, -1, 1)}


def tail_numerator(hist, n):
    """Return B=kappa*n^3=max_j j^2 #{g:k_g>=j}."""
    total = 0
    B = 0
    for j in range(n, 1, -1):
        total += hist[j]
        B = max(B, j * j * total)
    return B


def colors(P):
    out = Counter()
    for p in P:
        for q in P:
            if p != q:
                out[norm(sub(p, q))] += 1
    return out


def grid_check(L):
    P = [(x, y) for x in range(-L, L + 1)
         for y in range(-L, L + 1)]
    Ps = set(P)
    n = len(P)
    r = colors(P)
    E = sum(v * v for v in r.values())
    displacement = Counter(sub(q, p) for p in P for q in P)
    shells = defaultdict(list)
    for v in displacement:
        if v != (0, 0):
            shells[norm(v)].append(v)
    rotations = set()
    for shell in shells.values():
        for z in shell:
            for w in shell:
                rotations.add(ratio(w, z))
    assert all(a * a + b * b == c * c for a, b, c in rotations)

    sigmas = {}
    angle_energies = {}
    rich_hist = Counter()
    column = Counter()
    carrier_k = {}
    checked_rows = 0
    for u in sorted(rotations):
        a, b, c = u
        fibres = defaultdict(list)
        for p in P:
            up_num = mul((a, b), p)
            for q in P:
                t_num = (c * q[0] - up_num[0], c * q[1] - up_num[1])
                fibres[t_num].append(p)
        sigma = len(fibres)
        sigmas[u] = sigma
        assert sum(map(len, fibres.values())) == n * n
        assert sum(len(Q) - 1 for Q in fibres.values()) == n * n - sigma
        eu = 0
        for Q in fibres.values():
            k = len(Q)
            assert len(set(Q)) == k
            if k >= 2:
                checked_rows += 1
                rich_hist[k] += 1
                eu += k * (k - 1)
                ar = colors(Q)
                assert sum(ar.values()) == k * (k - 1)
                column.update(ar)
        angle_energies[u] = eu
        carrier_k[u] = len(fibres.get((c, 0), ()))
    assert sum(angle_energies.values()) == E
    assert column == Counter({d: rd * rd for d, rd in r.items()})
    B = tail_numerator(rich_hist, n)
    assert B > 0

    # Any finite selected family of actual angle fibres obeys (3).
    rng = Random(1800 + L)
    sorted_u = sorted(rotations)
    selections = [sorted_u, sorted_u[:1], sorted_u[::2], sorted_u[::3]]
    for _ in range(8):
        selections.append(rng.sample(sorted_u, rng.randrange(1, len(sorted_u) + 1)))
    for U in selections:
        s = sum(sigmas[u] for u in U)
        deficit = len(U) * n * n - s
        assert deficit >= 0
        assert deficit * deficit <= 4 * B * s

    tested_thresholds = 0
    for T in sorted(set(sigmas.values())):
        if T >= n * n:
            continue
        m = sum(s <= T for s in sigmas.values())
        assert m * (n * n - T) ** 2 <= 4 * B * T
        assert m * n * n * (n * n - T) <= E * T
        if 2 * T <= n * n:
            assert m * n ** 4 <= 4 * B * T
        tested_thresholds += 1

    # Exact inherited-support energy lower bounds on sparse grid subsets.
    # These test the ingredients of the restricted sparse-grid RS case,
    # not a universal RS assertion or an asymptotic constant.
    for divisor in (2, 3, 4):
        small = rng.sample(P, max(2, n // divisor))
        ns = len(small)
        rs = colors(small)
        es = sum(v*v for v in rs.values())
        inherited_lower = sum((max(Fraction(0), Fraction(ns**4, sigma)-ns*ns)
                               for sigma in sigmas.values()), Fraction(0))
        assert inherited_lower <= es
        for u in sorted_u[::max(1, len(sorted_u)//12)]:
            a, b, c = u
            small_support = {(c*q[0]-(a*p[0]-b*p[1]),
                              c*q[1]-(b*p[0]+a*p[1]))
                             for p in small for q in small}
            assert len(small_support) <= sigmas[u]

    # Whole rich 0 -> 1 carrier, excluding the four Gaussian units.
    carrier = [u for u in sorted_u if carrier_k[u] >= 2]
    nonunits = [u for u in carrier if u not in UNITS]
    for u in nonunits:
        for v in nonunits:
            if u != v:
                assert angle_difference(u, v)[2] != 1

    # Two-to-one commutator map and capacities, on a still larger angle set.
    comm = Counter(angle_difference(u, v) for u in sorted_u for v in sorted_u if u != v)
    assert max(comm.values(), default=0) <= 2
    assert 2 * len(comm) >= len(sorted_u) * (len(sorted_u) - 1)
    supported_pairs = 0
    point_mass = 0
    color_mass = Counter()
    W_comm = Fraction(0)
    for t, mult_t in comm.items():
        a, b, c = t
        if c != 1:
            continue
        kval = displacement.get((a, b), 0)
        if kval:
            supported_pairs += mult_t
            point_mass += mult_t * kval
            color_mass[a * a + b * b] += mult_t * kval
        Q = [p for p in P if add(p, (a, b)) in Ps]
        at = colors(Q)
        Wt = sum((Fraction(ad, r[d] ** 2) for d, ad in at.items()), Fraction(0))
        W_comm += mult_t * Wt
    assert supported_pairs <= 2 * (len(displacement) - 1)
    assert supported_pairs == 12  # precisely the distinct Gaussian-unit pairs
    assert point_mass == 48 * L * L - 4
    assert point_mass <= 2 * n * (n - 1)
    assert all(v <= 2 * r[d] for d, v in color_mass.items())
    W_id = sum((Fraction(1, rd) for rd in r.values()), Fraction(0))
    assert W_comm <= 2 * (n - 2) * W_id

    # Check the actual four-fold affine product, not only the formula.
    for _ in range(30):
        u, v = rng.sample(sorted_u, 2)
        g = (u, (Fraction(1), Fraction(0)))
        h = (v, (Fraction(1), Fraction(0)))
        word = affine_mul(affine_mul(affine_mul(g, h), affine_inv(g)), affine_inv(h))
        a, b, c = angle_difference(u, v)
        assert word == ((1, 0, 1), (Fraction(a, c), Fraction(b, c)))

    total_carrier_mass = sum(max(k - 1, 0) for k in carrier_k.values())
    print(f"grid L={L}: n={n}, D={len(r)}, E={E}, angles={len(rotations)}, "
          f"rich rows={checked_rows}, kappa={float(Fraction(B,n**3)):.6f}")
    print(f"  {tested_thresholds} support thresholds; carrier rich angles={len(carrier)}, "
          f"nonunits={len(nonunits)}, carrier mass={total_carrier_mass}; "
          f"all {len(nonunits)*(len(nonunits)-1)} nonunit commutators unsupported; "
          f"exactly {supported_pairs} supported unit pairs")


def nearest_integer(a, b):
    q, r = divmod(a, b)
    return q + (2 * r > b)


def gaussian_gcd(a, b):
    while b != (0, 0):
        numerator = mul(a, conj(b))
        den = norm(b)
        q = (nearest_integer(numerator[0], den), nearest_integer(numerator[1], den))
        a, b = b, sub(a, mul(q, b))
    return a


def count_gaussian_map(L, alpha, beta, source_center=(0, 0), target_center=(1, 0)):
    """Count via z=source_center+beta*w, without enumerating a huge grid."""
    assert norm(alpha) == norm(beta)
    assert norm(gaussian_gcd(alpha, beta)) == 1
    R = isqrt((2 * (L + 2) ** 2) // norm(beta)) + 2
    Q = set()
    image = set()
    for x in range(-R, R + 1):
        for y in range(-R, R + 1):
            w = (x, y)
            z = add(source_center, mul(beta, w))
            target = add(target_center, mul(alpha, w))
            if max(abs(z[0]), abs(z[1]), abs(target[0]), abs(target[1])) <= L:
                Q.add(z)
                image.add(target)
    assert len(Q) == len(image)
    return Q, image


def quotient_family_check(m, K):
    T = 100 * factorial(m)
    while True:
        L = T * T // 100
        betas = [(T * j, -1) for j in range(1, m + 1)]
        domains = []
        images = []
        for beta in betas:
            Q, I = count_gaussian_map(L, conj(beta), beta)
            domains.append(Q)
            images.append(I)
        if min(map(len, domains)) >= K:
            break
        T *= 2
    us = [ratio(conj(b), b) for b in betas]
    for j, ell in combinations(range(m), 2):
        bj, bl = betas[j], betas[ell]
        assert norm(gaussian_gcd(bj, bl)) == 1
        assert domains[j] & domains[ell] == {(0, 0)}
        assert images[j] & images[ell] == {(1, 0)}
        numerator = mul(conj(bl), bj)
        denominator = mul(bl, conj(bj))
        assert norm(gaussian_gcd(numerator, denominator)) == 1
        assert norm(denominator) == norm(bj) * norm(bl)
        assert norm(denominator) > 2 * (L + 1) ** 2
        Q0, _ = count_gaussian_map(L, numerator, denominator, (0, 0), (0, 0))
        Q1, _ = count_gaussian_map(L, numerator, denominator, (1, 0), (1, 0))
        assert Q0 == {(0, 0)}
        assert Q1 == {(1, 0)}
        assert angle_difference(us[j], us[ell])[2] != 1
    print(f"quotient family m={m}, K={K}: T={T}, L={L}, "
          f"richnesses={[len(Q) for Q in domains]}; all distinct quotients have k=1")


def field_check(q, check_columns=True):
    assert q % 4 == 3
    rng = Random(4200 + q)
    delta = log(q) / q
    P = [(x, y) for x in range(q) for y in range(q) if rng.random() < delta]
    assert len(P) >= 2
    Ps = set(P)
    n = len(P)
    H = [(a, b) for a in range(q) for b in range(q) if (a*a + b*b) % q == 1]
    assert len(H) == q + 1
    r = Counter()
    for p in P:
        for s in P:
            if p != s:
                d = norm(sub(p, s)) % q
                assert d != 0
                r[d] += 1
    E = sum(v*v for v in r.values())
    hist = Counter()
    columns = Counter()
    total_points = 0
    total_energy = 0
    support_sum = 0
    nonidentity_counts = []
    for a, b in H:
        fibre_points = 0
        fibre_support = 0
        for x in range(q):
            for y in range(q):
                Q = [p for p in P
                     if ((a*p[0]-b*p[1]+x) % q,
                         (b*p[0]+a*p[1]+y) % q) in Ps]
                k = len(Q)
                fibre_points += k
                fibre_support += k > 0
                hist[k] += 1
                total_energy += k*(k-1)
                if (a,b,x,y) != (1,0,0,0):
                    nonidentity_counts.append(k)
                else:
                    assert k == n
                if check_columns:
                    for p in Q:
                        for s in Q:
                            if p != s:
                                d = norm(sub(p, s)) % q
                                assert d != 0
                                columns[d] += 1
        assert fibre_points == n*n
        assert fibre_support <= q*q
        total_points += fibre_points
        support_sum += fibre_support
    assert sum(hist.values()) == q*q*(q+1)
    assert total_points == (q+1)*n*n
    assert total_energy == E
    if check_columns:
        assert columns == Counter({d: rd*rd for d, rd in r.items()})
    B = tail_numerator(hist, n)
    deficit = (q+1)*n*n-support_sum
    assert deficit*deficit <= 4*B*support_sum
    if n > q:
        assert (q+1)*(n*n-q*q)**2 <= 4*B*q*q
    if 2*q*q <= n*n:
        assert (q+1)*n**4 <= 4*B*q*q
    print(f"finite field q={q}: n={n}, D={len(r)}, E={E}, "
          f"ED^2/n^5={float(Fraction(E*len(r)**2,n**5)):.6f}, "
          f"kappa={float(Fraction(B,n**3)):.6f}, log(q)={log(q):.6f}")
    print(f"  nonidentity k range [{min(nonidentity_counts)}, {max(nonidentity_counts)}], "
          f"full table columns={'checked' if check_columns else 'not expanded'}, "
          f"point and energy identities exact")


def main():
    print('Exact support-sensitive motion checks')
    for L in (1, 2, 3, 4):
        grid_check(L)
    for m, K in ((2, 8), (3, 12), (4, 20)):
        quotient_family_check(m, K)
    for q in (7, 11, 19, 31):
        field_check(q, check_columns=q <= 19)
    print('PASS: all exact assertions passed.')
    print('RS is unproved; finite-field examples are not real planar counterexamples.')


if __name__ == '__main__':
    main()
