#!/usr/bin/env python3
"""Exact finite checks for GrowingResidueExclusionAttempt.md.

No asymptotic or actual translated-prime estimate is inferred from these tests.
The last test uses prime flags of actual AUXILIARY integers with full factors.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, product
from math import factorial, gcd, prod


def subsets(n):
    return (tuple(i for i in range(n) if mask >> i & 1) for mask in range(1 << n))


def partitions(xs):
    if not xs:
        yield ()
        return
    a, *rest = xs
    for part in partitions(rest):
        yield ((a,),) + part
        for j in range(len(part)):
            yield part[:j] + ((a,) + part[j],) + part[j + 1:]


local_checks = 0
for p in (3, 5, 7, 11, 13, 17):
    for nu in range(1, min(p, 7)):
        t = Q(1, p - nu + 1)
        states = list(product((0, 1), repeat=nu))
        parent = {v: t ** sum(v) * (1 - t) ** (nu - sum(v)) for v in states}
        acceptance = sum(m for v, m in parent.items() if sum(v) <= 1)
        a = Q(p * (p - nu) ** (nu - 1), (p - nu + 1) ** nu)
        assert acceptance == a
        law = {v: m / a for v, m in parent.items() if sum(v) <= 1}
        assert law[(0,) * nu] == Q(p - nu, p)
        for j in range(nu):
            v = tuple(int(i == j) for i in range(nu))
            assert law[v] == Q(1, p)
        # Radon--Nikodym derivative constant 1/a on the allowed set:
        # this is exactly the entropy identity KL = -log(a).
        assert all(m / parent[v] == 1 / a for v, m in law.items())
        q = Q(1, p)
        raw_accept = (1 - q) ** (nu - 1) * (1 + (nu - 1) * q)
        assert q * (1 - q) ** (nu - 1) / raw_accept == Q(1, p + nu - 1)
        for S in subsets(nu):
            before = sum(m for v, m in parent.items() if all(v[j] == 0 for j in S))
            after = sum(m for v, m in law.items() if all(v[j] == 0 for j in S))
            assert before == (1 - t) ** len(S)
            assert after == 1 - Q(len(S), p)
            assert after / before >= 1
            local_checks += 1

# Shared-root covariance and distinct-root cumulants, by actual residues.
H = (0, 6, 30, 36)
cumulant_checks = 0
for p in (5, 7, 11, 13):
    rows = [tuple(int((a + h) % p == 0) for h in H) for a in range(p)]
    moment = {S: Q(sum(prod(row[i] for i in S) for row in rows), p) for S in subsets(len(H))}
    for i, j in product(range(len(H)), repeat=2):
        both = Q(sum(row[i] * row[j] for row in rows), p)
        cov = both - Q(1, p * p)
        assert cov == (Q(1, p) - Q(1, p * p) if (H[i] - H[j]) % p == 0 else -Q(1, p * p))
    for S in subsets(len(H)):
        if not S or len({H[i] % p for i in S}) != len(S):
            continue
        cumulant = sum((-1) ** (len(part) - 1) * factorial(len(part) - 1)
                       * prod(moment[tuple(sorted(block))] for block in part)
                       for part in partitions(list(S)))
        assert cumulant == Q((-1) ** (len(S) - 1) * factorial(len(S) - 1), p ** len(S))
        cumulant_checks += 1

# Full finite-prime CRT void probabilities, including p=5 shared roots.
P = (5, 7, 11)
modulus = prod(P)
void_checks = 0
for S in subsets(len(H)):
    crt_void = Q(sum(all((n + H[i]) % p for p in P for i in S) for n in range(modulus)), modulus)
    expected = prod(1 - Q(len({H[i] % p for i in S}), p) for p in P)
    before = prod((1 - Q(1, p - len({h % p for h in H}) + 1)) ** len({H[i] % p for i in S}) for p in P)
    assert crt_void == expected
    assert crt_void / before >= 1
    void_checks += 1

# Multiplicative finite-row bound, including rare residue events.
row_checks = 0
for modulus in range(2, 10):
    for R in range(1, 3 * modulus + 1):
        counts = Counter((4 + k) % modulus for k in range(R))
        rem = R % modulus
        tv = sum(abs(Q(counts[a], R) - Q(1, modulus)) for a in range(modulus)) / 2
        assert tv == Q(rem * (modulus - rem), R * modulus)
        assert tv <= Q(modulus, 4 * R)
        for S in subsets(modulus):
            actual = Q(sum(counts[a] for a in S), R)
            uniform = Q(len(S), modulus)
            assert abs(actual - uniform) <= Q(modulus, R) * uniform
            row_checks += 1

# Self-contained local-lemma conditional bound on a finite product space.
# These bits test the probability lemma, NOT a prime model.
q = Q(1, 100)
edges = tuple(combinations(range(4), 2))
x = 2 * q * q
bit_rows = []
for v in product((0, 1), repeat=4):
    mass = q ** sum(v) * (1 - q) ** (4 - sum(v))
    bad = sum((v[i] and v[j]) << e for e, (i, j) in enumerate(edges))
    bit_rows.append((v, bad, mass))
ll_checks = 0
for e in range(len(edges)):
    for mask in range(1 << len(edges)):
        if mask >> e & 1:
            continue
        denominator = sum(m for v, bad, m in bit_rows if not bad & mask)
        numerator = sum(m for v, bad, m in bit_rows if not bad & mask and bad >> e & 1)
        assert numerator / denominator <= x
        ll_checks += 1
pe = sum(m for v, bad, m in bit_rows if bad == 0)
for S in subsets(4):
    incident = sum(bool(set(S) & set(edge)) for edge in edges)
    for values in product((0, 1), repeat=len(S)):
        match = lambda v: tuple(v[i] for i in S) == values
        pf = sum(m for v, bad, m in bit_rows if match(v))
        pfe = sum(m for v, bad, m in bit_rows if match(v) and bad == 0)
        assert pfe / pe <= pf / (1 - x) ** incident
        ll_checks += 1


def factor(n):
    ans = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            ans[p] = ans.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        ans[n] = 1
    return ans


N, z, W = 120, 3, 6
U = tuple(m for m in range(N + 1, 2 * N + 1) if gcd(m, W) == 1)
factors = {m: factor(m) for m in U}
prime = {m: int(factors[m] == {m: 1}) for m in U}
sector = {s: tuple(m for m in U if (-1) ** sum(factors[m].values()) == s) for s in (-1, 1)}


def incompatible(i, j, a, b, powers=True):
    delta = abs(H[i] - H[j])
    # In this example, the only difference prime > z is 5, to exponent 1.
    relevant = set(factors[a]) | set(factors[b]) | set(factor(delta))
    for p in relevant:
        if p <= z:
            continue
        va, vb = factors[a].get(p, 0), factors[b].get(p, 0)
        if delta % p:
            if va and vb:
                return True
        else:
            assert delta % (p * p)
            if bool(va) != bool(vb):
                return True
            if powers and va >= 2 and vb >= 2:
                return True
    return False


# Squarefree compatibility alone misses this exact prime-power obstruction.
power_example = (125, 127, 175, 131)
assert not any(incompatible(i, j, power_example[i], power_example[j], False) for i, j in edges)
assert any(incompatible(i, j, power_example[i], power_example[j], True) for i, j in edges)

pair_bad = {(i, j): {(a, b): incompatible(i, j, a, b) for a in U for b in U} for i, j in edges}
branch_tables = []
sample_count = 0
accepted_counts = []
for active in (0, 1):
    domains = [sector[-1 if i // 2 == active else 1] for i in range(4)]
    table = Counter()
    for ys in product(*domains):
        bad = sum(pair_bad[i, j][ys[i], ys[j]] << e for e, (i, j) in enumerate(edges))
        flags = sum(prime[y] << i for i, y in enumerate(ys))
        assert not ((flags & 3) and (flags & 12))
        table[bad, flags] += 1
    total = prod(map(len, domains))
    accepted = sum(c for (bad, flags), c in table.items() if bad == 0)
    assert accepted > 0
    sample_count += total
    accepted_counts.append(accepted)
    pe = Q(accepted, total)
    for S in subsets(4):
        smask = sum(1 << i for i in S)
        off = sum(1 << e for e, edge in enumerate(edges) if not set(S) & set(edge))
        pf = Q(sum(c for (bad, flags), c in table.items() if flags & smask == smask), total)
        pe0 = Q(sum(c for (bad, flags), c in table.items() if not bad & off), total)
        pfe0 = Q(sum(c for (bad, flags), c in table.items() if not bad & off and flags & smask == smask), total)
        pfe = Q(sum(c for (bad, flags), c in table.items() if bad == 0 and flags & smask == smask), total)
        assert pfe0 == pf * pe0
        if pf:
            assert (pfe / pe) / pf == (pe0 / pe) * (pfe / pfe0)
        else:
            assert pfe == 0
    branch_tables.append((table, accepted))

# The repaired ensemble still has a positive actual-prime pair in each active
# branch and zero cross-pool prime flags. No asymptotic factor is tested here.
for S in ((0, 1), (2, 3), (0, 2), (1, 3)):
    smask = sum(1 << i for i in S)
    mixture = sum(Q(sum(c for (bad, flags), c in tab.items() if not bad and flags & smask == smask), 2 * accepted)
                  for tab, accepted in branch_tables)
    assert (mixture > 0) == (S in ((0, 1), (2, 3)))

example = (127, 131, 121, 169)
assert not any(pair_bad[i, j][example[i], example[j]] for i, j in edges)
assert len({y - h for y, h in zip(example, H)}) > 1
# Directly find common residues realizing all valuations at each relevant p.
for p in set().union(*(set(factors[y]) for y in example)):
    vals = [factors[y].get(p, 0) for y in example]
    vmax = max(vals)
    anchor = vals.index(vmax)
    base = (-H[anchor]) % (p ** vmax)
    def val_mod(a, h):
        v = 0
        while v <= vmax and (a + h) % (p ** (v + 1)) == 0:
            v += 1
        return v
    assert any([val_mod(base + t * p ** vmax, h) for h in H] == vals for t in range(p))
# Exceptional-prime lifting, including M > Z and roots covering every class.
HZ, Z = (0, 1, 2, 3, 5), 3
a = 1
while Z ** a <= max(HZ) - min(HZ):
    a += 1
qz = Z ** a
exception_checks = 0
for residue in range(qz):
    for extra in range(3):
        vals = []
        for h in HZ:
            v = 0
            while v < a and (residue + h) % (Z ** (v + 1)) == 0:
                v += 1
            vals.append(v + extra if v == a else v)
        vmax = max(vals)
        anchor = vals.index(vmax)
        base = (-HZ[anchor]) % (Z ** vmax)
        def matches(n):
            for h, v in zip(HZ, vals):
                if (n + h) % Z ** v or (n + h) % Z ** (v + 1) == 0:
                    return False
            return True
        assert any(matches(base + t * Z ** vmax) for t in range(Z))
        exception_checks += 1
for S in subsets(len(HZ)):
    no_hit = Q(sum(all((a0 + HZ[i]) % Z for i in S) for a0 in range(qz)), qz)
    assert no_hit == 1 - Q(len({HZ[i] % Z for i in S}), Z)
    exception_checks += 1



print(f'PASS: {local_checks} calibrated-void checks; {cumulant_checks} cumulants; {void_checks} multi-prime voids;')
print(f'      {row_checks} finite-row relative bounds; {ll_checks} exact local-lemma checks;')
print(f'      {sample_count} full-factorization auxiliary samples, accepted by branch: {accepted_counts};')
print(f'      {exception_checks} exceptional-prime lift/void checks; all deletion identities and prime-power repairs verified.')
print('Auxiliary integers are not common translates. No analytic asymptotic or prime-gap proof is tested.')
