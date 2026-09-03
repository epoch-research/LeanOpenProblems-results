#!/usr/bin/env python3
"""Finite audits for CubeTwoColourGlobalCompletion.md.

This does not test or assume the unproved global Ramsey implication.
All colour constraints in the resampling audit use ordinary injections.
"""
from collections import Counter, defaultdict
from itertools import combinations, permutations, product
from math import comb, exp, factorial, lgamma, log
from pathlib import Path
import hashlib
import random

RNG = random.Random(18120260902)
COUNTS = Counter()


def bits(mask, n):
    return [i for i in range(n) if mask >> i & 1]


def rainbow_tree(S, T, lists):
    """Exhaustive tree search, independent of the induction in the proof."""
    S = tuple(S)
    if len(S) == 1:
        assert not T
        return []
    choices = []
    for v in T:
        support = [y for y in S if v in lists[y]]
        choices.append(list(combinations(support, 2)))
    for edges in product(*choices):
        parent = {y: y for y in S}

        def root(y):
            while parent[y] != y:
                y = parent[y]
            return y

        ok = True
        for y, z in edges:
            ry, rz = root(y), root(z)
            if ry == rz:
                ok = False
                break
            parent[ry] = rz
        if ok and len({root(y) for y in S}) == 1:
            return list(zip(T, edges))
    raise AssertionError((S, T, lists))


def audit_hall_trees():
    for m in range(1, 5):
        for b in range(1, 5):
            # All systems for these ranges, including 2^16 systems at m=b=4.
            for code in range(1 << (m * b)):
                lists = [set(bits((code >> (b * y)) & ((1 << b) - 1), b))
                         for y in range(m)]
                deficient = []
                for sm in range(1, 1 << m):
                    S = bits(sm, m)
                    T = set().union(*(lists[y] for y in S))
                    if len(T) >= len(S):
                        continue
                    if any(old & sm == old for old in deficient):
                        continue
                    deficient.append(sm)
                    assert len(T) == len(S) - 1
                    TT = tuple(sorted(T))
                    for wm in range(1, 1 << len(TT)):
                        W = {TT[i] for i in bits(wm, len(TT))}
                        support = {y for y in S if lists[y] & W}
                        assert len(support) >= len(W) + 1
                    tree = rainbow_tree(S, TT, lists)
                    assert len(tree) == len(S) - 1
                    COUNTS['minimal Hall circuit trees'] += 1
                COUNTS['abstract list systems'] += 1


def cube(d):
    E = [x for x in range(1 << d) if x.bit_count() % 2 == 0]
    O = [y for y in range(1 << d) if y.bit_count() % 2 == 1]
    nb = {y: {y ^ (1 << i) for i in range(d)} for y in O}
    return E, O, nb


def syndrome(x, ell):
    ans = 0
    for i in range(ell):
        if x >> i & 1:
            ans ^= i
    return ans


def star_partition(d, S=frozenset()):
    """Choose the syndrome in each outer fibre to minimize roots in S."""
    ell = 1 << (d.bit_length() - 1)
    E, O, nb = cube(d)
    mask = (1 << ell) - 1
    roots = []
    for outer in range(1 << (d - ell)):
        possible = [y for y in O if y >> ell == outer]
        classes = [[y for y in possible if syndrome(y & mask, ell) == s]
                   for s in range(ell)]
        chosen = min(classes, key=lambda C: (sum(y in S for y in C), C))
        roots.extend(chosen)
    blocks = [(r, {r ^ (1 << i) for i in range(ell)}) for r in roots]
    return ell, blocks


def audit_geometry():
    for d in range(1, 11):
        E, O, nb = cube(d)
        for S in [set(), set(O), {y for y in O if RNG.randrange(3) == 0}]:
            ell, blocks = star_partition(d, S)
            assert len(blocks) * ell == len(E)
            flat = [x for _, I in blocks for x in I]
            assert len(set(flat)) == len(flat) and set(flat) == set(E)
            assert ell * sum(r in S for r, _ in blocks) <= len(S)
            for r, I in blocks:
                assert len(I) == ell
                counts = Counter()
                for y in O:
                    J = nb[y] & I
                    counts[len(J)] += 1
                    if y != r:
                        assert len(J) <= 2
                    if len(J) == 2:
                        assert (y >> ell) == (r >> ell)
                    COUNTS['source block/row intersections'] += 1
                assert nb[r] & I == I
        for y, z in combinations(O, 2):
            common = len(nb[y] & nb[z])
            assert common == (2 if (y ^ z).bit_count() == 2 else 0)
            assert len(nb[y] | nb[z]) >= 2 * d - 2
            COUNTS['source pair intersections'] += 1


def host(N):
    red = [set() for _ in range(N)]
    for a, b in combinations(range(N), 2):
        if RNG.randrange(2):
            red[a].add(b)
            red[b].add(a)
    return red


def edge(red, a, b, c):
    assert a != b
    return (b in red[a]) if c == 0 else (b not in red[a])


def lists_for(f, B, nb, red, c):
    return {y: {b for b in B if all(edge(red, f[x], b, c) for x in nb[y])}
            for y in nb}


def choose_witness(lists, O):
    candidates = []
    for _ in range(50):
        size = RNG.randrange(1, len(O) + 1)
        S = set(RNG.sample(O, size))
        T = set().union(*(lists[y] for y in S))
        if len(T) < len(S):
            candidates.append((S, T))
    if not candidates:
        return None
    return RNG.choice(candidates)


def residual_data(d, I, pinned, B, S, T, nb, red, c):
    data = []
    for y in S:
        J = nb[y] & I
        K = {b for b in B - T
             if all(edge(red, pinned[x], b, c) for x in nb[y] - I)}
        data.append((y, J, K))
    return data


def audit_resampling():
    # Exhaustive resampling within each sampled actual-host conditional state.
    # No claim that any of these small hosts is a large-C countercolouring.
    for d, a, b, trials in [(3, 7, 6, 80), (4, 11, 10, 100), (5, 20, 18, 40)]:
        E, O, nb = cube(d)
        A, B = set(range(a)), set(range(a, a + b))
        for _ in range(trials):
            red = host(a + b)
            f = dict(zip(E, RNG.sample(sorted(A), len(E))))
            witnesses = []
            for c in (0, 1):
                W = choose_witness(lists_for(f, B, nb, red, c), O)
                if W is None:
                    break
                S, T = W
                # Pad the target set to |S|-1. This audits the relaxed fibre
                # identity without imposing canonical-certificate minimality.
                T |= set(RNG.sample(sorted(B - T), len(S) - 1 - len(T)))
                witnesses.append((S, T))
            if len(witnesses) != 2:
                continue
            SS = witnesses[0][0] | witnesses[1][0]
            ell, blocks = star_partition(d, SS)
            root, I = RNG.choice(blocks)
            II = sorted(I)
            pinned = {x: f[x] for x in E if x not in I}
            A0 = A - set(pinned.values())
            data = [residual_data(d, I, pinned, B, S, T, nb, red, c)
                    for c, (S, T) in enumerate(witnesses)]
            outside = B - witnesses[0][1] - witnesses[1][1]
            for v in outside:
                active = [set(), set()]
                for c in (0, 1):
                    for y, J, K in data[c]:
                        if y != root and 1 <= len(J) <= 2 and v in K:
                            active[c] |= J
                # Same-index opposite constraints would disagree on a
                # common pinned cube neighbour; valid for d >= 3.
                assert not (active[0] & active[1])
                COUNTS['signed active-support disjointness tests'] += 1
            allowed = []
            for values in permutations(sorted(A0), ell):
                full = pinned | dict(zip(II, values))
                direct = True
                binary = True
                for c, (S, T) in enumerate(witnesses):
                    L = lists_for(full, B, nb, red, c)
                    direct &= all(L[y] <= T for y in S)
                    for _, J, K in data[c]:
                        binary &= not any(all(edge(red, full[x], v, c) for x in J)
                                          for v in K)
                assert direct == binary
                if direct:
                    allowed.append(values)
                COUNTS['actual injective resamplings'] += 1
            assert allowed  # The original f is always a legal resampling.
            forced_positions = set()
            rectangle_found = False
            for pos, i in enumerate(II):
                support = {values[pos] for values in allowed}
                for c in (0, 1):
                    W = set()
                    for _, J, K in data[1 - c]:
                        if J == {i}:
                            W |= K
                    assert all(edge(red, a0, v, c) for a0 in support for v in W)
                    COUNTS['literal forced rectangles'] += 1
                    if len(W) >= len(E):
                        forced_positions.add(pos)
                        if len(support) >= len(E):
                            rectangle_found = True
                            COUNTS['forced-rectangle cube completions'] += 1
            if not rectangle_found:
                n = len(A0)
                beta = ell * log(n) - log(fall(n, ell))
                deficit = log(fall(n, ell)) - log(len(allowed))
                penalty = len(forced_positions) * log(n / (len(E) - 1)) - beta
                assert deficit >= penalty - 1e-9
                COUNTS['unary conditional entropy bounds'] += 1
            COUNTS['actual-host conditional states'] += 1


def fall(n, k):
    if k < 0 or k > n:
        return 0
    ans = 1
    for i in range(k):
        ans *= n - i
    return ans


def clique_count(n, edges, j):
    if j == 0:
        return 1
    return factorial(j) * sum(
        all(tuple(sorted((a, b))) in edges for a, b in combinations(S, 2))
        for S in combinations(range(n), j))


def audit_zykov():
    for n in range(1, 6):
        pairs = list(combinations(range(n), 2))
        for code in range(1 << len(pairs)):
            edges = {pairs[i] for i in bits(code, len(pairs))}
            counts = [clique_count(n, edges, j) for j in range(n + 1)]
            q = max(j for j in range(n + 1) if counts[j])
            for j in range(n + 1):
                assert counts[j] * q ** j <= n ** j * fall(q, j)
                COUNTS['Zykov clique-count inequalities'] += 1


def audit_positive_completion_bound():
    # All red bipartite relations on 4+4 sites, plus larger random tests.
    cases = []
    for code in range(1 << 16):
        sets = [set(bits((code >> (4 * i)) & 15, 4)) for i in range(4)]
        cases.append((2, 2, 4, sets))
    for _ in range(500):
        sets = [{v for v in range(8) if RNG.randrange(2)} for _ in range(8)]
        cases.append((3, 2, 8, sets))
    for d, ell, k, sets in cases:
        m = 1 << (d - 1)
        n = len(sets)
        D = (k - m) // d
        good = [i for i, S in enumerate(sets) if len(S) <= D]
        if len(good) >= m:
            # Literal parity embedding in the complementary colour.
            E, O, nb = cube(d)
            f = dict(zip(E, good[:m]))
            used = set()
            for y in O:
                options = set(range(k)) - used
                for x in nb[y]:
                    options -= sets[f[x]]
                assert options
                used.add(min(options))
            COUNTS['actual complementary cube completions'] += 1
        else:
            g = len(good)
            q = k // (D + 1)
            count = sum(all(not (sets[i] & sets[j]) for i, j in combinations(seq, 2))
                        for seq in permutations(range(n), ell))
            # Multiply through by q^ell to keep the audit integral.
            rhs = sum(comb(ell, j) * fall(g, ell - j) * (n - g) ** j
                      * fall(q, j) * q ** (ell - j)
                      for j in range(ell + 1))
            assert count * q ** ell <= rhs
            COUNTS['positive local clique-fibre bounds'] += 1


def entropy(counter):
    total = sum(counter.values())
    return -sum((v / total) * log(v / total) for v in counter.values())


def audit_pair_entropy_profile():
    # The numerical corollary's worst permitted p, using log-sum-exp.
    for exponent in range(3, 11):
        ell = 1 << exponent
        p = exp(-16)
        for q in sorted({1, ell // 2, ell, 2 * ell, 4 * ell}):
            logs = []
            for j in range(min(ell, q) + 1):
                term = (lgamma(ell + 1) - lgamma(j + 1) - lgamma(ell - j + 1)
                        + (ell - j) * log(p)
                        + lgamma(q + 1) - lgamma(q - j + 1) - j * log(q))
                logs.append(term)
            peak = max(logs)
            value = peak + log(sum(exp(x - peak) for x in logs))
            assert value <= log(2) - ell / 64 + 1e-8
            COUNTS['pair-entropy numerical profiles'] += 1


def audit_global_entropy_ledger():
    for a, m in [(3, 2), (4, 3), (5, 3)]:
        ambient = list(permutations(range(a), m))
        families = []
        if len(ambient) <= 6:
            families = [[ambient[i] for i in bits(mask, len(ambient))]
                        for mask in range(1, 1 << len(ambient))]
        else:
            for _ in range(300):
                families.append(RNG.sample(ambient, RNG.randrange(1, len(ambient) + 1)))
        partitions = [[(i,) for i in range(m)], [tuple(range(m - 1)), (m - 1,)]]
        for F in families:
            H = log(len(F))
            deficit = log(fall(a, m)) - H
            for blocks in partitions:
                cond = []
                base = []
                for I in blocks:
                    other = tuple(i for i in range(m) if i not in I)
                    marg = Counter(tuple(f[i] for i in other) for f in F)
                    cond.append(H - entropy(marg))
                    base.append(log(fall(a - m + len(I), len(I))))
                gamma = H - sum(cond)
                xi = log(fall(a, m)) - sum(base)
                local = sum(b - c for b, c in zip(base, cond))
                assert gamma >= -1e-10 and xi >= -1e-10
                assert abs(local - (deficit + gamma - xi)) < 1e-9
                assert all(c <= b + 1e-10 for b, c in zip(base, cond))
                COUNTS['global/conditional entropy identities'] += 1
    for m in range(1, 101):
        b = 3 * m
        cat = sum(comb(m, s) * comb(b, s - 1) for s in range(1, m + 1))
        assert cat == comb(b + m, m - 1)
        assert cat * 27 ** m <= 256 ** m
        COUNTS['joint certificate-catalogue bounds'] += 1


def main():
    spec = Path(__file__).with_name('Spec.lean')
    before = hashlib.sha256(spec.read_bytes()).hexdigest()
    assert before == '9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b'
    audit_hall_trees()
    audit_geometry()
    audit_resampling()
    audit_zykov()
    audit_positive_completion_bound()
    audit_pair_entropy_profile()
    audit_global_entropy_ledger()
    after = hashlib.sha256(spec.read_bytes()).hexdigest()
    assert before == after
    for key in sorted(COUNTS):
        print(f'{key}: {COUNTS[key]:,}')
    print('Spec.lean SHA-256:', after)
    print('PASS: stated finite identities and positive local lemmas.')
    print('NOT PROVED/TESTED: global certificate-to-cube/cut implication; R(Q_d)=O(2^d).')


if __name__ == '__main__':
    main()
