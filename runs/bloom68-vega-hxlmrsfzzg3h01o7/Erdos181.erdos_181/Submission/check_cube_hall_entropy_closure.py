#!/usr/bin/env python3
"""Exact finite audits for CubeHallEntropyClosureAttempt.md.

Entropy expressions are prime-log vectors with rational coefficients; equalities
and the entropy inequalities tested here use integer/rational arithmetic only.
No asymptotic Ramsey conclusion, tensorization, or residual-supply premise is
assumed.  Actual-host tests include successful injections (a GOOD key); they
are not asserted to be global countercolourings.
"""
from collections import Counter, defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations, permutations
from math import comb, lcm
from pathlib import Path
import hashlib
import random

RNG = random.Random(18190603)
COUNTS = Counter()
SPEC_HASH = '9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b'


@lru_cache(None)
def fall(n, r):
    if r < 0 or r > n:
        return 0
    ans = 1
    for j in range(r):
        ans *= n - j
    return ans


@lru_cache(None)
def factors(n):
    assert n > 0
    out = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def add(*forms):
    out = defaultdict(Q)
    for form in forms:
        for p, x in form.items():
            out[p] += x
    return {p: x for p, x in out.items() if x}


def scale(q, form):
    return {p: Q(q) * x for p, x in form.items() if q * x}


def logq(q):
    q = Q(q)
    assert q > 0
    return add(factors(q.numerator), scale(-1, factors(q.denominator)))


def entropy(counts):
    vals = [Q(v) for v in counts if v]
    total = sum(vals)
    return add(logq(total), *[scale(-v / total, logq(v)) for v in vals])


def nonnegative(form):
    """Compare exp(L*form) with 1, exactly, for common denominator L."""
    den = lcm(*(x.denominator for x in form.values())) if form else 1
    pos = neg = 1
    for p, x in form.items():
        power = int(x * den)
        if power >= 0:
            pos *= p ** power
        else:
            neg *= p ** (-power)
    return pos >= neg


def kl(p, q):
    return add(*[scale(v, logq(v / q[x])) for x, v in p.items() if v])


def marginal(family, coords):
    return Counter(tuple(f[i] for i in coords) for f in family)


def heat_law(family, ambient, erased, m, a):
    remaining = tuple(i for i in range(m) if i not in erased)
    marg = marginal(family, remaining)
    denominator = len(family) * fall(a - len(remaining), len(erased))
    return {f: Q(marg[tuple(f[i] for i in remaining)], denominator)
            for f in ambient if marg[tuple(f[i] for i in remaining)]}


def audit_nested_heat_baths():
    for a, m in [(3, 2), (4, 3), (5, 3), (5, 4)]:
        ambient = list(permutations(range(a), m))
        if len(ambient) == 6:
            families = [[ambient[i] for i in range(6) if mask >> i & 1]
                        for mask in range(1, 64)]
        else:
            families = [RNG.sample(ambient, RNG.randrange(1, len(ambient) + 1))
                        for _ in range(24)]
        mu = {f: Q(1, len(ambient)) for f in ambient}
        orders = [[(i,) for i in range(m)], [tuple(range(m))],
                  [tuple(range(m - 1)), (m - 1,)]]
        for family in families:
            for order in orders:
                erased = set()
                prev = heat_law(family, ambient, erased, m, a)
                total_production = {}
                for I in order:
                    remaining = tuple(i for i in range(m) if i not in erased)
                    new_remaining = tuple(i for i in remaining if i not in I)
                    h_old = entropy(marginal(family, remaining).values())
                    h_new = entropy(marginal(family, new_remaining).values())
                    predicted = add(logq(fall(a - len(new_remaining), len(I))),
                                    scale(-1, h_old), h_new)
                    erased.update(I)
                    nxt = heat_law(family, ambient, erased, m, a)
                    assert sum(prev.values()) == sum(nxt.values()) == 1
                    # Apply the actual joint heat-bath to the current law,
                    # rather than only recomputing the next law from P.
                    outside_mass = defaultdict(Q)
                    for f, weight in prev.items():
                        outside_mass[tuple(f[i] for i in new_remaining)] += weight
                    applied = {f: outside_mass[tuple(f[i] for i in new_remaining)]
                               / fall(a - len(new_remaining), len(erased))
                               for f in ambient
                               if outside_mass[tuple(f[i] for i in new_remaining)]}
                    assert applied == nxt
                    production = add(kl(prev, mu), scale(-1, kl(nxt, mu)))
                    assert predicted == production == kl(prev, nxt)
                    assert production == add(entropy(nxt.values()),
                                             scale(-1, entropy(prev.values())))
                    assert nonnegative(production)
                    total_production = add(total_production, production)
                    prev = nxt
                    COUNTS['exact joint heat-bath production identities'] += 1
                assert prev == mu
                assert total_production == logq(Q(len(ambient), len(family)))
                # Audit the exact relation to the old all-other-blocks ledger.
                H = logq(len(family))
                sum_all_H = {}
                sum_local_base = {}
                sum_cmi = {}
                prefix = ()
                prefix_H = {}
                for I in order:
                    outside = tuple(i for i in range(m) if i not in I)
                    all_H = add(H, scale(-1, entropy(marginal(family, outside).values())))
                    next_prefix = prefix + I
                    next_H = entropy(marginal(family, next_prefix).values())
                    cmi = add(next_H, scale(-1, prefix_H), scale(-1, all_H))
                    assert nonnegative(cmi)
                    sum_cmi = add(sum_cmi, cmi)
                    sum_all_H = add(sum_all_H, all_H)
                    sum_local_base = add(sum_local_base, logq(fall(a - m + len(I), len(I))))
                    prefix, prefix_H = next_prefix, next_H
                gamma = add(H, scale(-1, sum_all_H))
                xi = add(logq(len(ambient)), scale(-1, sum_local_base))
                all_deficits = add(sum_local_base, scale(-1, sum_all_H))
                assert gamma == sum_cmi
                assert nonnegative(xi)
                assert add(all_deficits, scale(-1, total_production)) == add(gamma, scale(-1, xi))
                COUNTS['exact old-Gamma versus production ledger identities'] += 1
                COUNTS['complete nested erasure chains'] += 1


def cube(d):
    E = [x for x in range(1 << d) if x.bit_count() % 2 == 0]
    O = [x for x in range(1 << d) if x.bit_count() % 2 == 1]
    index = {x: i for i, x in enumerate(E)}
    nb = [frozenset(index[y ^ (1 << j)] for j in range(d)) for y in O]
    ell = 1 << (d.bit_length() - 1)
    roots = []
    for y in O:
        syndrome = 0
        for j in range(ell):
            if y >> j & 1:
                syndrome ^= j
        if syndrome == 0:
            roots.append(y)
    atoms = [frozenset(index[y ^ (1 << j)] for j in range(ell)) for y in roots]
    assert set().union(*atoms) == set(range(len(E)))
    assert sum(map(len, atoms)) == len(E)
    return E, O, nb, list(zip(roots, atoms))


def indices(mask, n):
    return [i for i in range(n) if mask >> i & 1]


def hall_key(lists, m):
    for sm in sorted(range(1, 1 << m), key=lambda x: (x.bit_count(), x)):
        tm = 0
        for y in indices(sm, m):
            tm |= lists[y]
        if tm.bit_count() < sm.bit_count():
            assert tm.bit_count() == sm.bit_count() - 1
            return sm, tm
    return None


def actual_key(f, adj, nb, b):
    full = (1 << b) - 1
    keys = []
    for c in (0, 1):
        lists = []
        for N in nb:
            L = full
            for i in N:
                L &= adj[f[i]] if c == 0 else full ^ adj[f[i]]
            lists.append(L)
        key = hall_key(lists, len(nb))
        if key is None:
            return ('GOOD',)
        keys.append(key)
    return tuple(keys)


def monochromatic_cube(d, evens, candidates, adj, colour, b):
    """Produce and check a literal greedy parity embedding in the host cut."""
    E, O, nb, _ = cube(d)
    assert len(evens) >= len(E)
    f = tuple(evens[:len(E)])
    used = set()
    odd_images = []
    for N in nb:
        options = [v for v in candidates if v not in used and
                   all(((adj[f[i]] >> v) & 1) == (1 - colour) for i in N)]
        assert options
        v = min(options)
        used.add(v)
        odd_images.append(v)
    assert len(set(f)) == len(E) and len(set(odd_images)) == len(O)
    # A and B are disjoint host pools; all d*m source edges were checked.
    COUNTS['literal complementary or unary cube extractions'] += 1


@lru_cache(None)
def U(n, r, g, q):
    return sum(Q(comb(r, j) * fall(g, r - j) * (n - g) ** j * fall(q, j), q ** j)
               for j in range(r + 1))


@lru_cache(None)
def cap(n, r, m, q):
    return min(Q(fall(n, r)), max(U(n, r, g, q) for g in range(min(n, m - 1) + 1)))


def audit_actual_prefix_fibres():
    cases = []
    # All cross-colour relations in this smallest range.
    for code in range(1 << 9):
        cases.append((2, 3, 3, [(code >> (3 * i)) & 7 for i in range(3)], code))
    for j in range(72):
        cases.append((3, 5, 8, [RNG.randrange(1 << 8) for _ in range(5)], j))
    for d, a, b, adj, case in cases:
        E, O, nb, atom_data = cube(d)
        m = len(E)
        full = (1 << b) - 1
        ambient = list(permutations(range(a), m))
        fibres = defaultdict(list)
        for f in ambient:
            fibres[actual_key(f, adj, nb, b)].append(f)
        E_mean = add(*[scale(Q(len(P), len(ambient)), logq(Q(len(ambient), len(P))))
                       for P in fibres.values()])
        assert E_mean == entropy([len(P) for P in fibres.values()])
        COUNTS['exact whole-cover key entropy identities (GOOD allowed)'] += 1
        for key, family in fibres.items():
            if key == ('GOOD',):
                continue
            atoms = ([frozenset([i]) for i in range(m)] if case % 3 == 0
                     else [I for _, I in atom_data])
            all_labels = {(c, y) for c in (0, 1) for y in indices(key[c][0], m)}

            def recurse(rows, pinned, unused_atoms, closed_before, spent_before):
                remaining = m - len(pinned)
                n = a - len(pinned)
                V = logq(Q(fall(n, remaining), len(rows)))
                if not remaining:
                    assert len(rows) == 1 and not V
                    assert closed_before == all_labels
                    assert len(spent_before) <= len(all_labels)
                    COUNTS['complete adaptive certificate-row schedules'] += 1
                    return V
                # Nonanticipating: only key, case, and already pinned values.
                offset = (sum(pinned.values()) + len(pinned) + case) % len(unused_atoms)
                chosen = [unused_atoms[offset]]
                if len(unused_atoms) > 1 and (len(pinned) + case) % 4 == 1:
                    chosen.append(unused_atoms[(offset + 1) % len(unused_atoms)])
                I = set().union(*chosen)
                coords = tuple(sorted(I))
                rest_atoms = [J for J in unused_atoms if J not in chosen]
                groups = defaultdict(list)
                for f in rows:
                    groups[tuple(f[i] for i in coords)].append(f)
                if len({len(P) for P in groups.values()}) > 1:
                    COUNTS['nonuniform completion-weighted next-batch laws'] += 1
                if len(chosen) > 1:
                    COUNTS['multi-atom reveal nodes'] += 1
                dist_entropy = entropy([len(P) for P in groups.values()])
                delta = add(logq(fall(n, len(I))), scale(-1, dist_entropy))
                assert nonnegative(delta)
                closed = {}
                old = set(pinned)
                for c, y in all_labels:
                    J = nb[y] & I
                    if J and nb[y] <= old | I:
                        K = full ^ key[c][1]
                        for i in nb[y] - I:
                            K &= adj[pinned[i]] if c == 0 else full ^ adj[pinned[i]]
                        closed[(c, y)] = (J, K)
                        for z in groups:
                            assignment = dict(pinned)
                            assignment.update(zip(coords, z))
                            lhs = full ^ key[c][1]
                            for i in nb[y]:
                                lhs &= adj[assignment[i]] if c == 0 else full ^ adj[assignment[i]]
                            rhs = K
                            for i in J:
                                rhs &= adj[assignment[i]] if c == 0 else full ^ adj[assignment[i]]
                            assert lhs == rhs == 0
                            COUNTS['exact signed closed-row residual identities'] += 1
                assert not (set(closed) & closed_before)
                if d >= 3:
                    for (c, y), (Jy, Ky) in closed.items():
                        if c != 0:
                            continue
                        for (cc, z), (Jz, Kz) in closed.items():
                            if cc != 1 or not (Ky & Kz) or not (Jy & Jz):
                                continue
                            if y == z:
                                assert nb[y] <= I
                            else:
                                common = nb[y] & nb[z]
                                assert len(common) == 2 and common <= I
                            COUNTS['actual opposite-colour square-closure checks'] += 1
                unused_hosts = set(range(a)) - set(pinned.values())
                units = []
                occupied = set()
                spent = set()
                # Literal unary rectangles, with a cap only when it is valid.
                for i in coords:
                    for desired in (0, 1):
                        witnesses = [(c, y) for (c, y), (J, K) in closed.items()
                                     if c == 1 - desired and J == {i} and K]
                        W = 0
                        for label in witnesses:
                            W |= closed[label][1]
                        if W.bit_count() < m:
                            continue
                        hosts = [u for u in unused_hosts if all(
                            ((adj[u] >> v) & 1) == 1 - desired for v in indices(W, b))]
                        if len(hosts) >= m:
                            monochromatic_cube(d, hosts, indices(W, b), adj, desired, b)
                            continue
                        if i not in occupied:
                            units.append(('unary', frozenset([i]), None))
                            occupied.add(i)
                            spent.add(witnesses[0])
                            COUNTS['valid observed unary units'] += 1
                # Full star pair units, and two-position subunits, at the same node.
                possible = [J for _, J in atom_data if J <= I and len(J) >= 2]
                possible += [frozenset(P) for P in combinations(coords, 2)]
                for Junit in sorted(set(possible), key=lambda J: (-len(J), tuple(sorted(J)))):
                    if Junit & occupied:
                        continue
                    for c in (0, 1):
                        K = full
                        labels = []
                        for pair in combinations(sorted(Junit), 2):
                            options = [label for label, (JJ, KK) in closed.items()
                                       if label[0] == c and JJ == set(pair)]
                            if not options:
                                break
                            label = min(options)
                            labels.append(label)
                            K &= closed[label][1]
                        else:
                            k = K.bit_count()
                            if k < m:
                                continue
                            D = (k - m) // d
                            q = k // (D + 1)
                            good = [u for u in unused_hosts if sum(
                                ((adj[u] >> v) & 1) == 1 - c for v in indices(K, b)) <= D]
                            if len(good) >= m:
                                monochromatic_cube(d, good, indices(K, b), adj, 1 - c, b)
                                continue
                            assert len(labels) == comb(len(Junit), 2)
                            units.append(('pair', Junit, q))
                            occupied.update(Junit)
                            spent.update(labels)
                            COUNTS['valid observed common-pair units'] += 1
                            break
                assert len(spent) == sum(1 if kind == 'unary' else comb(len(J), 2)
                                         for kind, J, _ in units)
                assert spent <= set(closed)
                assert not (spent & spent_before)
                # Exact product counting, without an s*log(n) relaxation or beta.
                bound = Q(1)
                pool = n
                price = {}
                for kind, J, q in units:
                    r = len(J)
                    C = Q(min(pool, m - 1)) if kind == 'unary' else cap(pool, r, m, q)
                    assert C > 0
                    bound *= C
                    price = add(price, logq(Q(fall(pool, r), C)))
                    pool -= r
                bound *= fall(pool, len(I) - len(occupied))
                assert Q(len(groups)) <= bound
                assert nonnegative(add(logq(bound), scale(-1, dist_entropy)))
                assert nonnegative(add(delta, scale(-1, price)))
                COUNTS['exact joint-unit count and entropy-price bounds'] += 1
                expected_child = {}
                for z, child_rows in groups.items():
                    new_pinned = dict(pinned)
                    new_pinned.update(zip(coords, z))
                    childV = recurse(child_rows, new_pinned, rest_atoms,
                                     closed_before | set(closed), spent_before | spent)
                    expected_child = add(expected_child, scale(Q(len(child_rows), len(rows)), childV))
                assert V == add(delta, expected_child)
                assert nonnegative(add(V, scale(-1, add(price, expected_child))))
                COUNTS['exact adaptive density-potential recursions'] += 1
                return V

            assert recurse(family, {}, atoms, set(), set()) == logq(Q(len(ambient), len(family)))
        COUNTS['actual bipartite host colourings'] += 1


def audit_joint_geometry():
    for d in range(3, 9):
        E, O, nb, atoms = cube(d)
        m = len(E)
        batches = [I for _, I in atoms]
        for _ in range(64):
            batches.append(frozenset().union(*(I for _, I in RNG.sample(
                atoms, RNG.randrange(1, min(len(atoms), 4) + 1)))))
        for I in batches:
            pinned = set(range(m)) - I
            for _ in range(8):
                red = {i for i in pinned if RNG.randrange(2)}
                active = {c: [y for y in range(m) if nb[y] & I and
                              (nb[y] - I <= (red if c == 0 else pinned - red))]
                          for c in (0, 1)}
                for y in active[0]:
                    for z in active[1]:
                        if not (nb[y] & nb[z] & I):
                            continue
                        if y == z:
                            assert nb[y] <= I
                        else:
                            assert len(nb[y] & nb[z]) == 2
                            assert nb[y] & nb[z] <= I
                        COUNTS['joint-batch opposite-sign intersection checks'] += 1
                for root, atom in atoms:
                    if I == atom:
                        yr = O.index(root)
                        R = set().union(*(nb[y] & I for y in active[0] if y != yr))
                        B = set().union(*(nb[y] & I for y in active[1] if y != yr))
                        assert not R & B
                        COUNTS['single-star non-root signed-disjointness checks'] += 1


def audit_pair_products():
    # Two disjoint pair units jointly injected into the same four-host pool.
    # All 2^16 actual A--K relations, not independent position marginals.
    n = k = 4
    d = m = r = 2
    D = (k - m) // d
    q = k // (D + 1)
    upper = cap(4, 2, m, q) * cap(2, 2, m, q)
    tuples = list(permutations(range(4)))
    for code in range(1 << 16):
        sets = [(code >> (4 * u)) & 15 for u in range(4)]
        good = [u for u in range(4) if sets[u].bit_count() <= D]
        if len(good) >= m:
            # The degree branch is itself a genuine complementary cube.
            monochromatic_cube(d, good, list(range(k)), sets, 1, k)
        else:
            allowed = sum(not (sets[z[0]] & sets[z[1]]) and not (sets[z[2]] & sets[z[3]])
                          for z in tuples)
            assert allowed <= upper
            COUNTS['exact two-pair-unit joint-injection counts'] += 1
    # Price ceiling: U >= (n)_r*(q)_r/q^r, even at the actual g.
    for d in range(2, 49):
        m = 1 << (d - 1)
        for k in (m, 2 * m, 3 * m):
            D = (k - m) // d
            q = k // (D + 1)
            assert q >= d
            for r in sorted({2, max(2, d // 2), d}):
                n = max(r, 2 * d)
                for g in sorted({0, min(n, m - 1), min(n // 2, m - 1)}):
                    lower = Q(fall(n, r) * fall(q, r), q ** r)
                    assert U(n, r, g, q) >= lower
                    assert cap(n, r, m, q) >= lower
                    COUNTS['exact pair-price ceiling inequalities'] += 1


def main():
    spec = Path(__file__).with_name('Spec.lean')
    before = hashlib.sha256(spec.read_bytes()).hexdigest()
    assert before == SPEC_HASH
    audit_nested_heat_baths()
    audit_actual_prefix_fibres()
    audit_joint_geometry()
    audit_pair_products()
    assert hashlib.sha256(spec.read_bytes()).hexdigest() == before
    for key in sorted(COUNTS):
        print(f'{key}: {COUNTS[key]:,}')
    print('Spec.lean SHA-256:', before)
    print('PASS: integer/rational audits; entropy identities use exact prime-log vectors.')
    print('NOT PROVED: a sufficient closed-residual surplus or global cube augmentation.')
    print('NO RAMSEY BOUND CLAIMED.')


if __name__ == '__main__':
    main()
