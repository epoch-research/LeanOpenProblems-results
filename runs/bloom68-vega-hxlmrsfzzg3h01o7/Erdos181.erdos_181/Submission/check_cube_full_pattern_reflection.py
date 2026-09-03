#!/usr/bin/env python3
"""Finite audits for CubeFullPatternReflection.md.

These checks audit identities and the fold operator. They do NOT prove the
missing maximum-relative reflection estimate or the Ramsey conjecture.
Only the Python standard library is used.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations, product
from math import factorial
import hashlib
import random


def parity(x):
    return x.bit_count() & 1


def cube_edges(d):
    return [(x, x ^ (1 << j))
            for x in range(1 << d) for j in range(d)
            if not (x & (1 << j))]


def pair_bits(x, i, j):
    return (x >> i) & 1, (x >> j) & 1


def replace_pair(x, i, j, a, b):
    return ((x & ~(1 << i) & ~(1 << j)) | (a << i) | (b << j))


def ordinary_fold(x, i, j, keep):
    # keep=0 retains 01; keep=1 retains 10 (bits ordered i,j).
    a, b = pair_bits(x, i, j)
    if a != b:
        a, b = (0, 1) if keep == 0 else (1, 0)
    return replace_pair(x, i, j, a, b)


def complementary_fold(x, i, j, keep):
    # keep=0 retains 00; keep=1 retains 11.
    a, b = pair_bits(x, i, j)
    if a == b:
        a = b = keep
    return replace_pair(x, i, j, a, b)


def edge_retraction(x, i, j, frozen, c):
    p = parity(x & ((1 << i) | (1 << j)))
    if frozen == i:
        return replace_pair(x, i, j, c, p ^ c)
    assert frozen == j
    return replace_pair(x, i, j, p ^ c, c)


def face_retraction(x, d, a, b, t):
    # t is a bit mask supported outside {a,b}.
    mask = (1 << d) - 1
    assert a != b and not (t & ((1 << a) | (1 << b)))
    return t | (x & (1 << a)) | (
        (parity(x & (mask ^ (1 << a))) ^ parity(t)) << b)


def two_block_colour(x, y, S, w):
    # w=(A0,A1,B0,B1); S and its complement are the two blocks.
    diff = x ^ y
    assert diff and diff & (diff - 1) == 0
    if diff & S:
        return w[parity(x & ~S)]
    return w[2 + parity(x & S)]


def reduced_type_from_face(colour, d, a, b, t):
    # R_{a,b,t}: the shift parity(t) may exchange A0,A1, which
    # is irrelevant to this exact translation-orbit quotient.
    c00 = t
    c10 = t | (1 << a)
    c01 = t | (1 << b)
    c11 = t | (1 << a) | (1 << b)
    return (colour(c00, c10) + colour(c01, c11),
            colour(c00, c01) + colour(c10, c11))


def mono_distribution(pair):
    out = Counter()
    for c in pair:
        out[(2 * c, 2 * c)] += Fraction(1, 2)
    return out


def add_scaled(out, other, scale):
    for key, value in other.items():
        out[key] += scale * value


def clean(counter):
    return {key: value for key, value in counter.items() if value}


def expected_P(w, d, s=1):
    D = d * (d - 1)
    t = d - s
    out = Counter()
    add_scaled(out, mono_distribution(w[:2]), Fraction(s * (s - 1), D))
    add_scaled(out, mono_distribution(w[2:]), Fraction(t * (t - 1), D))
    out[(sum(w[:2]), sum(w[2:]))] += Fraction(s * t, D)
    out[(sum(w[2:]), sum(w[:2]))] += Fraction(s * t, D)
    return clean(out)


def expected_K(w, d):
    D = d * (d - 1)
    out = Counter()
    add_scaled(out, mono_distribution(w[:2]), Fraction(1, D))
    add_scaled(out, mono_distribution(w[2:]), Fraction(d*d - 3*d + 3, D))
    out[(sum(w[:2]), sum(w[2:]))] += Fraction(d - 2, D)
    out[(sum(w[2:]), sum(w[:2]))] += Fraction(d - 2, D)
    return clean(out)


def faces(d):
    for a in range(d):
        for b in range(d):
            if a == b:
                continue
            others = [j for j in range(d) if j not in (a, b)]
            for bits in product((0, 1), repeat=d-2):
                t = sum(bit << j for j, bit in zip(others, bits))
                yield a, b, t


def audit_maps():
    tested = 0
    for d in range(2, 7):
        E = cube_edges(d)
        for i, j in combinations(range(d), 2):
            compounds = set()
            for u, v in product((0, 1), repeat=2):
                R = tuple(complementary_fold(ordinary_fold(x, i, j, u),
                                             i, j, v)
                          for x in range(1 << d))
                compounds.add(R)
                assert all(parity(x) == parity(R[x]) for x in range(1 << d))
                assert all((R[x] ^ R[y]).bit_count() == 1 for x, y in E)
                assert all(R[R[x]] == R[x] for x in range(1 << d))
                tested += 1
            desired = {
                tuple(edge_retraction(x, i, j, frozen, c)
                      for x in range(1 << d))
                for frozen in (i, j) for c in (0, 1)
            }
            assert compounds == desired and len(compounds) == 4
        for a, b, t in faces(d):
            R = [face_retraction(x, d, a, b, t) for x in range(1 << d)]
            assert len(set(R)) == 4
            assert all(R[R[x]] == R[x] for x in range(1 << d))
            assert all(parity(x) == parity(R[x]) for x in range(1 << d))
            assert all((R[x] ^ R[y]).bit_count() == 1 for x, y in E)
            # Build the same retraction by deterministically merging all
            # coordinates except a into b. This verifies the affine formula.
            for x in range(1 << d):
                z = x
                for j in range(d):
                    if j not in (a, b):
                        z = edge_retraction(z, j, b, j, (t >> j) & 1)
                assert z == R[x]
            tested += 1
    print(f"Parity, edge preservation, idempotence, and composition: {tested} maps PASS")


def audit_operators():
    p_cases = k_cases = 0
    for d in range(2, 8):
        face_list = list(faces(d))
        for w in product((0, 1), repeat=4):
            for s in range(1, d):
                S = (1 << s) - 1
                colour = lambda x, y: two_block_colour(x, y, S, w)
                actual = Counter(reduced_type_from_face(colour, d, a, b, t)
                                 for a, b, t in face_list)
                actual = {key: Fraction(n, len(face_list)) for key, n in actual.items()}
                assert actual == expected_P(w, d, s), (d, s, w, actual)
                if d <= 5:
                    # Audit the exact phase rules (2.3)--(2.4), not merely
                    # the nine-state translation-orbit quotient.
                    Tmask = ((1 << d) - 1) ^ S
                    for p, q, t in face_list:
                        rp = bool(S & (1 << p))
                        rq = bool(S & (1 << q))
                        R = [face_retraction(x, d, p, q, t)
                             for x in range(1 << d)]
                        if rp and rq:
                            constant = w[parity(t & Tmask)]
                            want = lambda x, y: constant
                        elif not rp and not rq:
                            constant = w[2 + parity(t & S)]
                            want = lambda x, y: constant
                        else:
                            c = parity(t & (S if rp else Tmask))
                            v = w if rp else w[2:] + w[:2]
                            wp = (v[c], v[1 ^ c], v[2+c], v[2+(1 ^ c)])
                            want = lambda x, y: two_block_colour(x, y, 1 << p, wp)
                        for x, y in cube_edges(d):
                            assert colour(R[x], R[y]) == want(x, y)
                p_cases += 1
            # The targeted extra compound fold Q, followed by P.
            actual = Counter()
            old_a = 0
            for j in range(1, d):
                for frozen in (old_a, j):
                    for c in (0, 1):
                        def colour(x, y):
                            ex = edge_retraction(x, old_a, j, frozen, c)
                            ey = edge_retraction(y, old_a, j, frozen, c)
                            return two_block_colour(ex, ey, 1 << old_a, w)
                        for a, b, t in face_list:
                            actual[reduced_type_from_face(colour, d, a, b, t)] += 1
            denom = 4 * (d - 1) * len(face_list)
            actual = {key: Fraction(n, denom) for key, n in actual.items()}
            expected = expected_K(w, d)
            assert actual == expected, (d, w, actual, expected)
            if len(set(w)) > 1:
                nonmono = sum(v for key, v in actual.items()
                              if key not in ((0, 0), (2, 2)))
                assert nonmono == Fraction(2 * (d - 2), d * (d - 1))
            k_cases += 1
    print(f"Exact P on all 16 square patterns and every block size: {p_cases} cases PASS")
    print(f"Exact symmetrized K on all 16 square patterns: {k_cases} cases PASS")


def audit_voter_implementation():
    # Audit the affine update and potential drift for every small label state.
    # Almost-sure absorption, expected stopping time, and the uniform terminal
    # face law are proved in the report, not inferred from a finite simulation.
    cases = 0
    for m in range(2, 6):
        for labels in product(range(m), repeat=m):
            if len(set(labels)) == 1:
                continue
            counts = Counter(labels)
            Z = sum(n*n for n in counts.values())
            for i, j in combinations(range(m), 2):
                if labels[i] == labels[j]:
                    continue
                next_Z = []
                for winner, loser in ((i, j), (j, i)):
                    new = list(labels)
                    new[loser] = labels[winner]
                    nc = Counter(new)
                    next_Z.append(sum(n*n for n in nc.values()))
                assert sum(next_Z) == 2 * (Z + 2)
                # Phases do not change labels. They add 0 or A_i+A_j.
                # Verify R o e directly, including nonzero affine constants.
                for const in (0, (1 << m) - 1):
                    def R(x):
                        y = const
                        for z in range(m):
                            if (x >> z) & 1:
                                y ^= 1 << labels[z]
                        return y
                    for frozen in (i, j):
                        winner = j if frozen == i else i
                        newlabels = list(labels)
                        newlabels[i] = newlabels[j] = labels[winner]
                        for c in (0, 1):
                            newconst = const ^ (c << labels[i]) ^ (c << labels[j])
                            for x in range(1 << m):
                                y = newconst
                                for z in range(m):
                                    if (x >> z) & 1:
                                        y ^= 1 << newlabels[z]
                                assert R(edge_retraction(x, i, j, frozen, c)) == y
                cases += 1

    print(f"Unbiased-fold voter update and exact +2 potential drift: {cases} cases PASS")


def full_counts(d, N, host):
    E = cube_edges(d)
    out = Counter()
    for f in permutations(range(N), 1 << d):
        sig = 0
        for k, (x, y) in enumerate(E):
            sig |= host[f[x]][f[y]] << k
        out[sig] += 1
    assert sum(out.values()) == factorial(N) // factorial(N - (1 << d))
    return out


def pullback_pattern(sig, E, R):
    index = {frozenset(e): k for k, e in enumerate(E)}
    out = 0
    for k, (x, y) in enumerate(E):
        out |= ((sig >> index[frozenset((R[x], R[y]))]) & 1) << k
    return out


def host_matrix(N, seed):
    rng = random.Random(seed)
    host = [[-1]*N for _ in range(N)]
    for x, y in combinations(range(N), 2):
        host[x][y] = host[y][x] = rng.randrange(2)
    return host


def exact_psd(A):
    """Exact rational Schur-complement certificate, including singular cases."""
    A = [[Fraction(x) for x in row] for row in A]
    while A:
        assert all(A[i][i] >= 0 for i in range(len(A)))
        pivot = next((i for i in range(len(A)) if A[i][i] > 0), None)
        if pivot is None:
            assert all(x == 0 for row in A for x in row)
            return
        others = [i for i in range(len(A)) if i != pivot]
        p = A[pivot][pivot]
        A = [[A[i][j] - A[i][pivot]*A[pivot][j]/p
              for j in others] for i in others]


def audit_joint_sector_matrix(d, N, E, T):
    # One ordinary reflection; all boundary and half-colour sectors.
    h, i, j = 1 << d, 0, 1
    rho = [replace_pair(x, i, j, (x >> j)&1, (x >> i)&1)
           for x in range(h)]
    F = {x for x in range(h) if rho[x] == x}
    U = {x for x in range(h) if x < rho[x]}
    edge_index = {frozenset(e): k for k, e in enumerate(E)}
    EF = [k for k, (x, y) in enumerate(E) if x in F and y in F]
    EA = [k for k, (x, y) in enumerate(E)
          if x in F | U and y in F | U and not (x in F and y in F)]
    EB = [edge_index[frozenset((rho[E[k][0]], rho[E[k][1]]))] for k in EA]
    H = 1 << len(EA)
    matrices = {}
    for sig, count in T.items():
        gamma = sum(((sig >> k)&1) << z for z, k in enumerate(EF))
        alpha = sum(((sig >> k)&1) << z for z, k in enumerate(EA))
        beta = sum(((sig >> k)&1) << z for z, k in enumerate(EB))
        C = matrices.setdefault(gamma, [[0]*H for _ in range(H)])
        C[alpha][beta] += count
    r, n = h//4, N-h//2
    for C in matrices.values():
        assert all(C[a][b] == C[b][a] for a in range(H) for b in range(H))
        R = [sum(row) for row in C]
        S = sum(R)
        # (n-r) S [ C + q diag(R) - (1+q) R R^t / S ]
        certificate = [[(n-r)*S*C[a][b] - n*R[a]*R[b]
                        + (r*S*R[a] if a == b else 0)
                        for b in range(H)] for a in range(H)]
        exact_psd(certificate)
    return len(matrices)


def audit_injective_reflection():
    audited = joint_audited = 0
    for d, N, seed in ((2, 6, 132), (3, 8, 913), (3, 9, 729)):
        host = host_matrix(N, seed)
        E = cube_edges(d)
        T = full_counts(d, N, host)
        joint_audited += audit_joint_sector_matrix(d, N, E, T)
        h = 1 << d
        selected = {0, (1 << len(E)) - 1, max(T, key=T.get)}
        selected.update(sorted(T, key=T.get, reverse=True)[:4])
        for i, j in combinations(range(d), 2):
            for complementary in (False, True):
                if complementary:
                    rho = [replace_pair(x, i, j, 1-((x >> j)&1),
                                        1-((x >> i)&1)) for x in range(h)]
                else:
                    rho = [replace_pair(x, i, j, (x >> j)&1,
                                        (x >> i)&1) for x in range(h)]
                F = [x for x in range(h) if rho[x] == x]
                U = [x for x in range(h) if x < rho[x]]
                V = [rho[x] for x in U]
                assert len(F) == h//2 and len(U) == len(V) == h//4
                assert not any(x in U and y in V or x in V and y in U for x, y in E)
                R_U = [rho[x] if x in V else x for x in range(h)]
                R_V = [rho[x] if x in U else x for x in range(h)]
                for sig in selected:
                    ab = aa = bb = vv = 0
                    for images in permutations(range(N), len(F)):
                        f = dict(zip(F, images))
                        if any(host[f[x]][f[y]] != ((sig >> k)&1)
                               for k, (x, y) in enumerate(E) if x in f and y in f):
                            continue
                        unused = [v for v in range(N) if v not in images]
                        a, b = Counter(), Counter()
                        for gi in permutations(unused, len(U)):
                            fa = f | dict(zip(U, gi))
                            fb = f | dict(zip(V, gi))
                            mask = sum(1 << z for z in gi)
                            if all(host[fa[x]][fa[y]] == ((sig >> k)&1)
                                   for k, (x, y) in enumerate(E) if x in fa and y in fa):
                                a[mask] += 1
                            if all(host[fb[x]][fb[y]] == ((sig >> k)&1)
                                   for k, (x, y) in enumerate(E) if x in fb and y in fb):
                                b[mask] += 1
                        masks = set(a) | set(b)
                        for S in masks:
                            for W in masks:
                                if S & W == 0:
                                    ab += a[S] * b[W]
                                    aa += a[S] * a[W]
                                    bb += b[S] * b[W]
                                    vv += (a[S]-b[S]) * (a[W]-b[W])
                    assert ab == T[sig]
                    assert aa == T[pullback_pattern(sig, E, R_U)]
                    assert bb == T[pullback_pattern(sig, E, R_V)]
                    assert 2*ab - aa - bb == -vv
                    audited += 1
        # Exact completion identity, grouped by all colours off S.
        subsets = [{0}, set(range(h//2)), {0, h-1}]
        for S in subsets:
            W = [x for x in range(h) if x not in S]
            kept = [(k, x, y) for k, (x, y) in enumerate(E) if x in W and y in W]
            direct = Counter()
            for im in permutations(range(N), len(W)):
                f = dict(zip(W, im))
                eta = sum(host[f[x]][f[y]] << k for k, x, y in kept)
                direct[eta] += 1
            grouped = Counter()
            mask = sum(1 << k for k, x, y in kept)
            for sig, n in T.items():
                grouped[sig & mask] += n
            falling = factorial(N-h+len(S)) // factorial(N-h)
            assert grouped == Counter({eta: n*falling for eta, n in direct.items()})
    print(f"Joint-sector PSD correction (exact rational certificates): {joint_audited} matrices PASS")
    print(f"Full-injection Kneser reflection identities: {audited} cases PASS")
    print("Full-injection completion identities (no relaxed maps counted as injections): PASS")


def main():
    path = 'Submission/Spec.lean'
    with open(path, 'rb') as f:
        digest = hashlib.sha256(f.read()).hexdigest()
    expected = '9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b'
    assert digest == expected, (digest, 'Spec.lean changed')
    print('Spec.lean SHA-256 unchanged:', digest)
    audit_maps()
    audit_operators()
    audit_voter_implementation()
    audit_injective_reflection()
    print('All finite audits PASS. Missing global reflection estimate NOT established.')


if __name__ == '__main__':
    main()
