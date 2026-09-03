#!/usr/bin/env python3
"""Exact and numerical checks for CubeGeneralCoreProgress.md.

This does NOT certify the unresolved all-support negative-activity inequality.
Exact rational checks verify the normalization, resummations, finite-population
corrections, and example kernels. Analytic all-order estimates are proved in the
Markdown file, not inferred from these finite tests.

Run: python3 Submission/check_cube_general_core.py
Only this script's stdout is written by shell redirection; Spec.lean is read-only.
"""
from __future__ import annotations

import cmath
import hashlib
import itertools as it
import math
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parent
SPEC_SHA = "9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b"


def bits(mask):
    return tuple(i for i in range(mask.bit_length()) if mask >> i & 1)


def submasks(mask):
    s = mask
    while True:
        yield s
        if s == 0:
            return
        s = (s - 1) & mask


def partitions(items):
    items = tuple(items)
    if not items:
        yield ()
        return
    first, tail = items[0], items[1:]
    for pi in partitions(tail):
        yield ((first,),) + pi
        for j in range(len(pi)):
            yield pi[:j] + ((first,) + pi[j],) + pi[j + 1:]


def connected(k, edges):
    if k == 0:
        return False
    seen = {0}
    while True:
        old = len(seen)
        for a, b in edges:
            if a in seen:
                seen.add(b)
            if b in seen:
                seen.add(a)
        if len(seen) == old:
            return len(seen) == k


def components(k, edges):
    parent = list(range(k))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for a, b in edges:
        parent[find(a)] = find(b)
    return len({find(x) for x in range(k)})


def mul(a, b):
    """Product in a commuting square-free / nilpotent variable algebra."""
    c = defaultdict(F)
    for i, ai in a.items():
        for j, bj in b.items():
            if not i & j:
                c[i | j] += ai * bj
    return {i: x for i, x in c.items() if x}


def inv(a, m):
    assert a.get(0) == 1
    u = {i: -x for i, x in a.items() if i}
    ans, power = {0: F(1)}, {0: F(1)}
    for _ in range(m):
        power = mul(power, u)
        for i, x in power.items():
            ans[i] = ans.get(i, F(0)) + x
    return {i: x for i, x in ans.items() if x}


def cumulants(moments, k):
    """Coefficients of log(sum_S Z(S) x_S), using the rooted recurrence."""
    assert moments[0] == 1
    w = {0: F(0)}
    for size in range(1, k + 1):
        for vertices in it.combinations(range(k), size):
            s = sum(1 << v for v in vertices)
            anchor = s & -s
            val = moments.get(s, F(0))
            for t in submasks(s):
                if t != s and t & anchor:
                    val -= w[t] * moments.get(s ^ t, F(0))
            w[s] = val
    return w


def from_cumulants(w, k):
    z = {0: F(1)}
    for size in range(1, k + 1):
        for vertices in it.combinations(range(k), size):
            s = sum(1 << v for v in vertices)
            anchor = s & -s
            z[s] = sum(w[t] * z[s ^ t] for t in submasks(s) if t & anchor)
    return z


class Host:
    def __init__(self, n, edges):
        self.n = n
        self.A = [[0] * n for _ in range(n)]
        for a, b in edges:
            assert a != b
            self.A[a][b] = self.A[b][a] = 1
        self.p = F(sum(map(sum, self.A)), n * (n - 1))
        assert self.p > 0
        self.M = [[F(0) if x == y else F(self.A[x][y]) / self.p - 1
                   for y in range(n)] for x in range(n)]
        assert sum(map(sum, self.M)) == 0
        self.rho = [sum(row) / n for row in self.M]
        self.a = [[F(x) / self.p for x in row] for row in self.A]

    def q(self, x, y, z=F(1)):
        return F(0) if x == y else 1 + z * self.M[x][y]


class Source:
    """All induced-subset moments, independently computed by injection sums."""
    def __init__(self, host, k, edges, z=F(1)):
        self.host, self.k, self.z = host, k, z
        self.edges = tuple(tuple(sorted(e)) for e in edges)
        assert len(set(self.edges)) == len(self.edges)
        self.assignments = {}
        self.moments = {}
        n = host.n
        for s in range(1 << k):
            vs = bits(s)
            es = [(a, b) for a, b in self.edges if (s >> a & 1) and (s >> b & 1)]
            rows = []
            for ys in it.permutations(range(n), len(vs)):
                phi = dict(zip(vs, ys))
                weight = F(1, n ** len(vs))
                for a, b in es:
                    weight *= host.q(phi[a], phi[b], z)
                    if not weight:
                        break
                if weight:
                    rows.append((phi, weight))
            self.assignments[s] = rows
            self.moments[s] = sum((w for _, w in rows), F(0))
        self.w = cumulants(self.moments, k)
        assert from_cumulants(self.w, k) == self.moments

    @property
    def activity(self):
        return self.w[(1 << self.k) - 1]

    def delta(self, vertices, g):
        """Connected response to ONE extra hyperedge with factor 1+g."""
        t = sum(1 << v for v in vertices)
        assert t
        modified = dict(self.moments)
        for s, rows in self.assignments.items():
            if s & t == t:
                modified[s] += sum((w * g(phi) for phi, w in rows), F(0))
        return cumulants(modified, self.k)[(1 << self.k) - 1] - self.activity


@lru_cache(None)
def connected_pair_graphs(k):
    pairs = tuple(it.combinations(range(k), 2))
    return tuple(tuple(pairs[j] for j in range(len(pairs)) if mask >> j & 1)
                 for mask in range(1 << len(pairs))
                 if connected(k, [pairs[j] for j in range(len(pairs)) if mask >> j & 1]))


def direct_activity(host, k, edges, z):
    """Original connected signed graph sum, NOT obtained by cumulants."""
    es = set(tuple(sorted(e)) for e in edges)
    answer = F(0)
    for labels in it.product(range(host.n), repeat=k):
        fs = {(a, b): -F(labels[a] == labels[b])
              + (z * host.M[labels[a]][labels[b]] if (a, b) in es else 0)
              for a, b in it.combinations(range(k), 2)}
        for graph in connected_pair_graphs(k):
            prod = F(1)
            for edge in graph:
                prod *= fs[edge]
                if not prod:
                    break
            answer += prod
    return answer / host.n ** k


def check_normalization_and_isolates(hosts):
    direct_checks = 0
    small_sources = [(2, [(0, 1)]), (3, [(0, 1), (0, 2)]),
                     (4, [(0, 1), (1, 2), (2, 3), (0, 3)]),
                     (4, [(0, 1), (2, 3)])]
    for host in hosts[:2]:
        for k, edges in small_sources:
            for z in (F(0), F(1, 2), F(1)):
                src = Source(host, k, edges, z)
                assert src.activity == direct_activity(host, k, edges, z)
                direct_checks += 1
    dressing_checks = 0
    bases = [(1, []), (2, [(0, 1)]), (3, [(0, 1), (1, 2)]),
             (4, [(0, 1), (2, 3)]), (4, [(0, 1), (1, 2), (2, 3), (0, 3)])]
    for host in hosts:
        for k, edges in bases:
            for z in (F(0), F(1, 2), F(1)):
                w0 = Source(host, k, edges, z).activity
                for j in range(5):
                    actual = Source(host, k + j, edges, z).activity
                    rising = math.prod(range(k, k + j))
                    expected = F((-1) ** j * rising, host.n ** j) * w0
                    assert actual == expected, (k, j, z, actual, expected)
                    dressing_checks += 1
    return direct_checks, dressing_checks


def cover_phi(src, core, outside, active_mask):
    """Host occupation-product formula; a square-free variable for each leaf."""
    host, n = src.host, src.host.n
    active = tuple(core[i] for i in bits(active_mask))
    active_set = set(active)
    core_edges = [(a, b) for a, b in src.edges if a in active_set and b in active_set]
    nbrs = {v: tuple(u for u in active if tuple(sorted((u, v))) in src.edges)
            for v in outside}
    ans = defaultdict(F)
    for labels in it.permutations(range(n), len(active)):
        phi = dict(zip(active, labels))
        weight = F(1, n ** len(active))
        for a, b in core_edges:
            weight *= host.q(phi[a], phi[b], src.z)
        if not weight:
            continue
        poly = {0: F(1)}
        used = set(labels)
        for y in range(n):
            if y in used:
                continue
            fac = {0: F(1)}
            for j, v in enumerate(outside):
                q = F(1, n)
                for u in nbrs[v]:
                    q *= host.q(phi[u], y, src.z)
                fac[1 << j] = q
            poly = mul(poly, fac)
        for mon, coeff in poly.items():
            ans[mon] += weight * coeff
    return {mon: coeff for mon, coeff in ans.items() if coeff}


def check_cover_formula(hosts):
    cases = [
        (5, [(0, 1), (0, 2), (0, 3), (1, 4)], (0, 1)),
        (6, [(0, 2), (0, 3), (1, 4), (1, 5)], (0, 1)),
        (5, [(0, 2), (1, 2), (0, 3), (1, 3)], (0, 1)),
        (6, [(0, 3), (1, 3), (1, 4), (2, 4), (0, 5), (2, 5)], (0, 1, 2)),
    ]
    cube_edges = [(x, x ^ (1 << j)) for x in range(8) for j in range(3)
                  if x < (x ^ (1 << j))]
    cases.append((8, cube_edges, tuple(x for x in range(8) if x.bit_count() % 2 == 0)))
    checked_moments = checked_connected = 0
    for host in hosts[:2]:
        for k, edges, core in cases:
            outside = tuple(v for v in range(k) if v not in core)
            assert all(a in core or b in core for a, b in edges)
            for z in (F(0), F(1, 2), F(1)):
                src = Source(host, k, edges, z)
                phi = {a: cover_phi(src, core, outside, a) for a in range(1 << len(core))}
                for a, poly in phi.items():
                    for j in range(1 << len(outside)):
                        whole = sum(1 << core[i] for i in bits(a))
                        whole |= sum(1 << outside[i] for i in bits(j))
                        assert poly.get(j, F(0)) == src.moments[whole]
                        checked_moments += 1
                dinv = inv(phi[0], len(outside))
                psi = {a: mul(poly, dinv) for a, poly in phi.items()}
                wc = defaultdict(F)
                for pi in partitions(range(len(core))):
                    prod = {0: F(1)}
                    for block in pi:
                        prod = mul(prod, psi[sum(1 << i for i in block)])
                    mu = (-1) ** (len(pi) - 1) * math.factorial(len(pi) - 1)
                    for mon, coeff in prod.items():
                        wc[mon] += mu * coeff
                for j in range(1 << len(outside)):
                    whole = sum(1 << v for v in core)
                    whole |= sum(1 << outside[i] for i in bits(j))
                    assert wc.get(j, F(0)) == src.w[whole]
                    checked_connected += 1
    return checked_moments, checked_connected


def check_vertex_elimination(hosts):
    cases = [(1, [], (0,)), (2, [(0, 1)], (0,)),
             (3, [(0, 1), (1, 2)], (0,)),
             (3, [(0, 1), (1, 2)], (0, 2)),
             (3, [], (0, 1, 2)),
             (4, [(0, 1), (1, 2), (2, 3), (0, 3)], (0, 1, 2, 3))]
    checks = 0
    for host in hosts:
        n, M = host.n, host.M
        for k, edges, neighbors in cases:
            src = Source(host, k, edges)
            target = Source(host, k + 1, edges + [(a, k) for a in neighbors]).activity
            rhs = -F(k, n) * src.activity
            for size in range(1, len(neighbors) + 1):
                for t in it.combinations(neighbors, size):
                    def gamma(phi, t=t):
                        return sum((math.prod(M[phi[a]][y] for a in t)
                                    for y in range(n)), F(0)) / n
                    rhs += src.delta(t, gamma)
                    for v in range(k):
                        if v in t:
                            continue
                        def collision(phi, t=t, v=v):
                            return math.prod(M[phi[a]][phi[v]] for a in t)
                        rhs -= src.delta(t + (v,), collision) / n
            assert rhs == target, (host.n, k, edges, neighbors, target, rhs)
            checks += 1
            if len(neighbors) == 1:
                a = neighbors[0]
                leaf_rhs = src.delta((a,), lambda phi: host.rho[phi[a]])
                boosted_sum = src.activity
                for v in range(k):
                    if v == a:
                        continue
                    # Extra factor a_xy, including a SECOND copy on an existing edge.
                    boosted_sum += src.activity + src.delta(
                        (a, v), lambda phi, v=v: host.a[phi[a]][phi[v]] - 1)
                leaf_rhs -= boosted_sum / n
                assert leaf_rhs == target
    regular = hosts[1]
    assert not any(regular.rho)
    src = Source(regular, 2, [])
    gamma_response = src.delta((0, 1), lambda phi: sum(
        regular.M[phi[0]][y] * regular.M[phi[1]][y]
        for y in range(regular.n)) / regular.n)
    frob = sum(x * x for row in regular.M for x in row)
    assert gamma_response == -frob / regular.n ** 3 < 0
    return checks, gamma_response, Source(regular, 3, [(0, 1), (0, 2)]).activity


def bivariate_mul(a, b, rr, ss):
    c = defaultdict(F)
    for (i, j), x in a.items():
        for (u, v), y in b.items():
            if i + u <= rr and j + v <= ss:
                c[i + u, j + v] += x * y
    return {ij: x for ij, x in c.items() if x}


def bivariate_power(a, exponent, rr, ss):
    result = {(0, 0): F(1)}
    for _ in range(exponent):
        result = bivariate_mul(result, a, rr, ss)
    return result


def check_two_centre_egf(hosts):
    checks = 0
    rr = ss = 3
    for host in hosts:
        n, a = host.n, host.a
        z1, z2, z12 = defaultdict(F), defaultdict(F), defaultdict(F)
        for x in range(n):
            p1 = p2 = {(0, 0): F(1)}
            for y in range(n):
                if y != x:
                    p1 = bivariate_mul(p1, {(0, 0): F(1), (1, 0): a[x][y] / n,
                                                (0, 1): F(1, n)}, rr, ss)
                    p2 = bivariate_mul(p2, {(0, 0): F(1), (1, 0): F(1, n),
                                                (0, 1): a[x][y] / n}, rr, ss)
            for ij, c in p1.items():
                z1[ij] += c / n
            for ij, c in p2.items():
                z2[ij] += c / n
            for y in range(n):
                if x == y or not a[x][y]:
                    continue
                poly = {(0, 0): F(1)}
                for z in range(n):
                    if z not in (x, y):
                        poly = bivariate_mul(poly, {(0, 0): F(1), (1, 0): a[x][z] / n,
                                                    (0, 1): a[y][z] / n}, rr, ss)
                for ij, c in poly.items():
                    z12[ij] += a[x][y] * c / n ** 2
        # D^{-1}=(1+(s+t)/n)^{-n}, with exact rising binomial coefficients.
        dinv = {}
        for r in range(rr + 1):
            for s in range(ss + 1):
                j = r + s
                dinv[r, s] = F((-1) ** j * math.prod(range(n, n + j)),
                               n ** j * math.factorial(r) * math.factorial(s))
        first = bivariate_mul(z12, dinv, rr, ss)
        second = bivariate_mul(bivariate_mul(z1, dinv, rr, ss),
                               bivariate_mul(z2, dinv, rr, ss), rr, ss)
        for r in range(rr + 1):
            for s in range(ss + 1):
                k = r + s + 2
                edges = [(0, 1)] + [(0, 2 + j) for j in range(r)]
                edges += [(1, 2 + r + j) for j in range(s)]
                actual = Source(host, k, edges).activity
                coefficient = first.get((r, s), F(0)) - second.get((r, s), F(0))
                assert actual == coefficient * math.factorial(r) * math.factorial(s)
                checks += 1
    return checks


def is_prime(n):
    if n < 2:
        return False
    return all(n % j for j in range(2, math.isqrt(n) + 1))


def paley_prime_at_least(n):
    q = n + (1 - n) % 4
    while not is_prime(q):
        q += 4
    return q


def check_two_centre_analytic_constants():
    e = math.e
    assert 35 * 4 * e * e / 4000 + 0.5 < 1
    assert 16 * 4 * e * e / 4000 + 0.25 < 0.5
    assert 126 + 3 * 32 < 250
    assert 128000 * e ** 3 < 3e6
    assert 40960 * e ** 2 / 9 < 34000
    ratios = []
    for d in (1, 2, 4, 8):
        n = paley_prime_at_least(4000 * d * d)
        R = 2 * e * d
        degree = (n - 1) // 2
        lam, mu = (n - 5) // 4, (n - 1) // 4
        bound = 250 * (1 + 0.25) * R * R / n  # Paley: L=1/2.
        for i, j in it.product(range(16), repeat=2):
            s = R * cmath.exp(2j * math.pi * i / 16)
            t = R * cmath.exp(2j * math.pi * j / 16)
            logd = n * cmath.log(1 + (s + t) / n)
            phi12 = (n - 1) / n * cmath.exp(
                lam * cmath.log(1 + 2 * (s + t) / n)
                + mu * cmath.log(1 + 2 * s / n)
                + mu * cmath.log(1 + 2 * t / n) - logd)
            phi1 = cmath.exp(degree * cmath.log(1 + t / n)
                              + degree * cmath.log(1 + (2 * s + t) / n) - logd)
            phi2 = cmath.exp(degree * cmath.log(1 + s / n)
                              + degree * cmath.log(1 + (s + 2 * t) / n) - logd)
            value = abs(phi12 - phi1 * phi2)
            assert value <= bound * (1 + 1e-10)
            ratios.append(value / bound)
    return len(ratios), max(ratios)


def check_dressing_majorant():
    checks = 0
    for h in range(2, 18):
        n = 20 * h
        x = math.e * h / n
        for k in range(2, h + 1):
            v_in_core = sum(math.comb(h - k, j) * math.prod(range(k, k + j))
                            * (math.e / n) ** j for j in range(h - k + 1))
            assert v_in_core <= (1 - x) ** (-k) * (1 + 1e-12)
            if h > k:
                v_outside = sum(math.comb(h - k - 1, j - 1) * math.prod(range(k, k + j))
                                * (math.e / n) ** j for j in range(1, h - k + 1))
                assert v_outside <= math.e * k / n * (1 - x) ** (-k - 1) * (1 + 1e-12)
            checks += 1
    return checks


def check_cube_skeleton_geometry():
    checked = 0
    for d in range(2, 6):
        parity = tuple(x for x in range(1 << d) if x.bit_count() % 2 == 0)
        other = tuple(x for x in range(1 << d) if x.bit_count() % 2)
        nbr_masks = [sum(1 << i for i, x in enumerate(parity)
                         if (x ^ y).bit_count() == 1) for y in other]
        for i, j in it.combinations(range(len(parity)), 2):
            assert sum((m >> i & 1) and (m >> j & 1) for m in nbr_masks) <= 2
        for s in range(1 << len(parity)):
            k = s.bit_count()
            if k < 2:
                continue
            m2 = sum((m & s).bit_count() == 2 for m in nbr_masks)
            assert 2 * m2 <= d * k
            assert m2 <= k * (k - 1)
            assert 2 * m2 <= (d + 2) * (k - 1)
            checked += 1
    tau = math.log(2) - 0.5 * math.log(1 + math.e)
    cconv = 4 * (1 + math.e) / tau ** 2
    cload = cconv + 27 * (1 + math.e) / (2 * math.e * tau ** 3)
    assert tau > 0
    assert cconv < 11200 and cload < 391000
    for d in range(1, 1001):
        assert d ** 2 <= F(9, 8) * 2 ** d
        assert d ** 3 <= 4 * 2 ** d
    return checked, tau, cconv, cload


def paley_host(n):
    assert n % 4 == 1 and is_prime(n)
    squares = {x * x % n for x in range(1, n)}
    return Host(n, [(x, y) for x in range(n) for y in range(x + 1, n)
                    if (x - y) % n in squares])


def matrix_density(kernel, k, edges, injective=False):
    n = len(kernel)
    assignments = it.permutations(range(n), k) if injective else it.product(range(n), repeat=k)
    return sum((math.prod(kernel[x[a]][x[b]] for a, b in edges)
                for x in assignments), F(0)) / n ** k


def flow_polynomial_value(n, k, edges):
    ans = 0
    for mask in range(1 << len(edges)):
        selected = [edges[j] for j in range(len(edges)) if mask >> j & 1]
        ans += (-1) ** (len(edges) - len(selected)) * n ** (
            len(selected) - k + components(k, selected))
    return ans


def count_nowhere_zero_flows(n, k, edges):
    """Independent count by chord values and leaf elimination in a spanning tree."""
    parent = list(range(k))

    def find(x):
        if parent[x] != x:
            parent[x] = find(parent[x])
        return parent[x]

    tree, chords = [], []
    for j, (a, b) in enumerate(edges):
        if find(a) == find(b):
            chords.append(j)
        else:
            parent[find(a)] = find(b)
            tree.append(j)
    assert len(tree) == k - 1
    count = 0
    for chord_values in it.product(range(n), repeat=len(chords)):
        values = [0] * len(edges)
        balance = [0] * k
        for j, q in zip(chords, chord_values):
            a, b = edges[j]
            values[j] = q
            balance[a] = (balance[a] + q) % n
            balance[b] = (balance[b] - q) % n
        remaining = set(tree)
        while remaining:
            incidence = [[] for _ in range(k)]
            for j in remaining:
                a, b = edges[j]
                incidence[a].append(j)
                incidence[b].append(j)
            leaf = next(v for v in range(k) if len(incidence[v]) == 1)
            j = incidence[leaf][0]
            a, b = edges[j]
            if leaf == a:
                q = -balance[a] % n
            else:
                q = balance[b] % n
            values[j] = q
            balance[a] = (balance[a] + q) % n
            balance[b] = (balance[b] - q) % n
            remaining.remove(j)
        assert not any(balance)
        count += all(values)
    return count


def check_gram_flows():
    cases = [(2, [(0, 1)]), (2, [(0, 1), (0, 1)]),
             (3, [(0, 1), (1, 2), (2, 0)]),
             (4, [(0, 1), (1, 2), (2, 3), (3, 0)]),
             (4, list(it.combinations(range(4), 2))),
             (6, [(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 5), (5, 3)])]
    checks = 0
    example = None
    for n in (5, 13):
        host = paley_host(n)
        gram = [[sum(host.M[x][z] * host.M[y][z] for z in range(n)) / n
                 for y in range(n)] for x in range(n)]
        assert all(gram[x][y] == F(x == y) - F(1, n)
                   for x in range(n) for y in range(n))
        for k, edges in cases:
            flows = flow_polynomial_value(n, k, edges)
            assert flows == count_nowhere_zero_flows(n, k, edges)
            density = F(flows, n ** len(edges))
            assert 0 <= density <= F(1, n ** (k - 1))
            if k <= 4:
                assert density == matrix_density(gram, k, edges)
            checks += 1
        triangle = [(0, 1), (1, 2), (2, 0)]
        bare = matrix_density(gram, 3, triangle)
        core_injective = matrix_density(gram, 3, triangle, injective=True)
        expected = F(math.prod(range(n - 2, n + 1)), n ** 3) * F(-1, n ** 3)
        assert bare > 0 and core_injective == expected < 0
        if n == 5:
            example = (bare, core_injective)
    return checks, example


def check_two_degenerate_certificate():
    # Q_4 levels 1 and 2: the once-subdivided K_4, an unbalanced min-degree-2 core.
    n = 401
    squares = {x * x % n for x in range(1, n)}
    A = np.array([[(x - y) % n in squares for y in range(n)] for x in range(n)], dtype=np.int64)
    M = 2 * A - np.ones((n, n), dtype=np.int64) + np.eye(n, dtype=np.int64)
    assert np.array_equal(M @ M, n * np.eye(n, dtype=np.int64) - np.ones((n, n), dtype=np.int64))
    codeg = A @ A
    good = codeg >= n / 8  # p^2 n/2, p=1/2.
    np.fill_diagonal(good, True)
    max_bad = int((~good).sum(axis=1).max())
    assert max_bad == 0
    pairs = list(it.combinations(range(4), 2))
    edges = [(a, 4 + j) for j, (a, b) in enumerate(pairs)]
    edges += [(b, 4 + j) for j, (a, b) in enumerate(pairs)]
    h, d = 10, 3
    assert n >= 36 * (h + max_bad * d * d + 1)
    nbrs = [set() for _ in range(h)]
    for a, b in edges:
        nbrs[a].add(b)
        nbrs[b].add(a)
    phi = {}
    for v in range(h):
        previous = nbrs[v] & phi.keys()
        assert len(previous) <= 2
        candidates = np.ones(n, dtype=bool)
        for u in previous:
            candidates &= A[phi[u]].astype(bool)
        assert int(candidates.sum()) >= n / 18
        for y in phi.values():
            candidates[y] = False
        for u in phi:
            if any(w > v for w in nbrs[v] & nbrs[u]):
                candidates &= good[phi[u]]
        choices = np.flatnonzero(candidates)
        assert choices.size
        phi[v] = int(choices[0])
    assert len(set(phi.values())) == h
    assert all(A[phi[a], phi[b]] for a, b in edges)
    return n, int(codeg[~np.eye(n, dtype=bool)].min()), phi


def main():
    spec_before = hashlib.sha256((ROOT / "Spec.lean").read_bytes()).hexdigest()
    assert spec_before == SPEC_SHA
    hosts = [
        Host(4, [(0, 1), (0, 2), (0, 3), (1, 2)]),
        Host(5, [(i, (i + 1) % 5) for i in range(5)]),
        Host(5, [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (2, 3)]),
    ]
    direct, isolate = check_normalization_and_isolates(hosts)
    print(f"PASS original connected signed sums versus log-cumulants: {direct} exact rational cases")
    print(f"PASS isolated-vertex rising-factorial dressing: {isolate} exact rational cases")
    moments, connected_checks = check_cover_formula(hosts)
    print(f"PASS arbitrary vertex-cover occupation formula: {moments} exact moment coefficients")
    print(f"PASS core-partition logarithm, including Q_3 and shared leaves: {connected_checks} exact activity coefficients")
    elimination, gamma_response, p3 = check_vertex_elimination(hosts)
    print(f"PASS general vertex deletion (degrees 1--4) and parallel-edge leaf response: {elimination} exact cases")
    print(f"CHECK PSD does not imply a positive connected response: C_5 host, Delta_Gamma={gamma_response}, w(P_3)={p3}")
    doubles = check_two_centre_egf(hosts)
    print(f"PASS two-centre EGF against direct moment-cumulants: {doubles} coefficients, both leaf counts 0--3")
    analytic_n, max_ratio = check_two_centre_analytic_constants()
    print(f"PASS analytic constant arithmetic; {analytic_n} complex-boundary Paley checks; max |W|/bound={max_ratio:.6g}")
    print(f"PASS finite isolated-dressing combinatorial majorants: {check_dressing_majorant()} cases")
    geometries, tau, cconv, cload = check_cube_skeleton_geometry()
    print(f"PASS cube pair-codegree and degree-two pool inequalities: {geometries} core subsets, dimensions 2--5")
    print(f"CHECK dimension-uniform skeleton constants: tau={tau:.12g}, C_conv={cconv:.9g}, C_load={cload:.9g}")
    flow_checks, example = check_gram_flows()
    print(f"PASS projection-Gram / nowhere-zero-flow identity: {flow_checks} all-size-class sample graphs, including bridges and parallel edges")
    print(f"CHECK even-cycle Gram positivity is not stable under core injectivity: bare={example[0]}, core-injective={example[1]}")
    n, min_codeg, phi = check_two_degenerate_certificate()
    print(f"PASS 2-degenerate positive-core embedding certificate: Q_4 levels 1,2 into Paley({n}), min off-diagonal codegree={min_codeg}, images={phi}")
    spec_after = hashlib.sha256((ROOT / "Spec.lean").read_bytes()).hexdigest()
    assert spec_after == spec_before
    print(f"PASS Spec.lean unchanged: {spec_after}")
    print("LIMITATION: no claim or verification of the full all-support cube negative-load bound.")


if __name__ == "__main__":
    main()
