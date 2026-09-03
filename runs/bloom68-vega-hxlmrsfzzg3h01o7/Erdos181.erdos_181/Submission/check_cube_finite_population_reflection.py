#!/usr/bin/env python3
"""Checks for CubeFinitePopulationReflection.md. No Lean dependencies.

The proof is in the accompanying note. Finite tests check the exact host
construction and formulas, rather than searching for Ramsey counterexamples.
"""
from __future__ import annotations

from collections import Counter, deque
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations, product
from math import comb, factorial, isqrt
from pathlib import Path
import hashlib
import random

import mpmath as mp
import numpy as np

ROOT = Path(__file__).resolve().parent
SPEC_HASH = "9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b"


def edges(d):
    return [(x, x ^ (1 << j)) for x in range(1 << d)
            for j in range(d) if not (x >> j) & 1]


def neighbours(x, d):
    return [x ^ (1 << j) for j in range(d)]


def falling(n, k):
    assert 0 <= k <= n
    return factorial(n) // factorial(n-k)


def fano_lines():
    lines = {tuple(sorted((x-1, y-1, (x ^ y)-1)))
             for x in range(1, 8) for y in range(x+1, 8)}
    assert len(lines) == 7
    return tuple(sorted(lines))


class Data:
    def __init__(self, a, k, lines):
        assert k >= a+2
        self.a, self.k = a, k
        self.m, self.u, self.r = 1 << a, 1 << (k-a), 1 << k
        self.lines = tuple(tuple(line) for line in lines)
        self.b = len(lines)
        self.ell = len(lines[0])
        self.p = max(max(line) for line in lines)+1
        assert all(len(line) == self.ell for line in lines)
        if self.b > 1:
            assert all(len(set(x) & set(y)) == 1 for x, y in combinations(lines, 2))
            assert set(Counter(p for line in lines for p in line).values()) == {self.ell}
        cells = [j for j in range(self.m) if j.bit_count() % 2 == 0]
        assert len(cells) >= self.b*self.ell
        self.alpha = {}
        self.markers = {}
        i = 0
        for L, line in enumerate(lines):
            for p in line:
                self.alpha[L, p] = cells[i]
                self.markers[cells[i]] = (L, p)  # extra coordinates zero
                i += 1
        self.D = i
        assert self.u >= self.ell
        self.fibres = [[z for z in range(self.r) if self.pi(z) == j]
                       for j in range(self.m)]
        assert all(len(f) == self.u for f in self.fibres)

    def pi(self, z):
        return (z & (self.m-1)) ^ ((z >> self.a).bit_count() % 2)

    def reduced_list(self, z):
        cell = self.pi(z)
        if z not in self.markers:
            return [("U", L, cell) for L in range(self.b)]
        L0, p = self.markers[z]
        return [("U", L, cell) for L in range(self.b) if L != L0] + [("P", p)]

    def compatible(self, x, y):
        if x[0] == y[0] == "U":
            return x[1] == y[1] and (x[2] ^ y[2]).bit_count() == 1
        if x[0] == "U":
            x, y = y, x
        if x[0] == "P" and y[0] == "U":
            p, L, j = x[1], y[1], y[2]
            return p in self.lines[L] and (j ^ self.alpha[L, p]).bit_count() == 1
        return False

    def check_phase_lemma(self):
        for x, y in edges(self.k):
            assert (self.pi(x) ^ self.pi(y)).bit_count() == 1
        for z in range(self.r):
            assert {self.pi(y) for y in neighbours(z, self.k)} == set(neighbours(self.pi(z), self.a))
        Z = set(self.markers)
        assert all(y not in Z for z in Z for y in neighbours(z, self.k))
        U = set(range(self.r)) - Z
        start = next(iter(U))
        visited = {start}
        queue = deque([start])
        while queue:
            for y in neighbours(queue.popleft(), self.k):
                if y in U and y not in visited:
                    visited.add(y)
                    queue.append(y)
        assert visited == U
        for L in range(self.b):
            for z, (L0, p) in self.markers.items():
                allowed = [x for x in self.reduced_list(z)
                           if all(self.compatible(x, ("U", L, self.pi(y)))
                                  for y in neighbours(z, self.k))]
                expected = [("P", p)] if L == L0 else [("U", L, self.pi(z))]
                assert allowed == expected, (L, z, allowed, expected)
        A = falling(2*self.u, self.u)
        ZL = A**self.m // (self.u+1)**self.ell
        assert A**self.m % (self.u+1)**self.ell == 0
        assert ZL == (falling(2*self.u, self.u)**(self.m-self.ell)
                      * falling(2*self.u, self.u-1)**self.ell)
        gamma = factorial(self.u)**(2*self.m) // self.u**(2*self.D)
        assert gamma == (factorial(self.u)**(2*(self.m-self.D))
                         * factorial(self.u-1)**(2*self.D))
        occupancy = Fraction(self.ell, self.b)
        assert occupancy >= Fraction(1, 2*self.b)
        if self.b > 1:
            assert sum(len(set(x) & set(y)) == 1 for x in self.lines for y in self.lines) == self.b*(self.b-1)
            for L, L2 in permutations(range(self.b), 2):
                p, = set(self.lines[L]) & set(self.lines[L2])
                z, z2 = self.alpha[L, p], self.alpha[L2, p]
                assert (z ^ z2).bit_count() >= 2
                assert 2 + (z ^ z2).bit_count() >= 4
        return ZL, gamma


class Host:
    def __init__(self, data, C):
        self.data = d = data
        self.n = n = 2*C*d.r
        self.N = N = 2*n+1
        self.sigma = (1, -1)
        pos = 0
        self.anchor = []
        self.private = []
        for c in range(2):
            A = np.arange(pos, pos+d.r).reshape(d.m, d.u)
            pos += d.r
            U = np.arange(pos, pos+2*d.b*d.r).reshape(d.b, d.m, 2*d.u)
            pos += 2*d.b*d.r
            self.anchor.append(A)
            self.private.append(U)
        self.points = [np.arange(pos+c*d.p, pos+(c+1)*d.p) for c in range(2)]
        pos += ((2*d.p+d.u-1)//d.u)*d.u
        self.free = np.arange(pos, pos+d.u)
        pos += d.u
        assert pos <= n, (pos, n)
        groups = np.arange(n)//d.u
        T = 1 << ((int(groups[-1])+1)-1).bit_length()
        self.T = T
        H = np.array([[1 if (x & y).bit_count() % 2 == 0 else -1
                       for y in range(T)] for x in range(T)], dtype=np.int8)
        assert np.array_equal(H.astype(np.int64) @ H.astype(np.int64).T, T*np.eye(T, dtype=np.int64))
        W = H[groups[:, None], groups[None, :]].copy()
        np.fill_diagonal(W, 0)
        S = np.zeros((N, N), dtype=np.int8)
        S[0:2*n:2, 0:2*n:2] = W
        S[0:2*n:2, 1:2*n:2] = -W
        S[1:2*n:2, 0:2*n:2] = -W
        S[1:2*n:2, 1:2*n:2] = W
        t = np.zeros(n, dtype=np.int8)
        t[self.anchor[0].ravel()] = 1
        t[self.anchor[1].ravel()] = -1
        remaining = np.flatnonzero(t == 0)
        assert len(remaining) % 2 == 0
        t[remaining[:len(remaining)//2]] = 1
        t[remaining[len(remaining)//2:]] = -1
        assert int(t.sum()) == 0
        for i in range(n):
            S[2*i, 2*i+1] = S[2*i+1, 2*i] = t[i]
            S[2*i, -1] = S[-1, 2*i] = -t[i]
            S[2*i+1, -1] = S[-1, 2*i+1] = -t[i]
        assert not np.any(S.sum(axis=1))
        self.S0 = S.copy()
        self.S = S
        self.used = {}
        self.anchor_lists = []
        self.position_lists = []
        self.special = []
        for c, sigma in enumerate(self.sigma):
            lists = {}
            special = {}
            for j in range(d.m):
                ordinary = set(map(int, self.private[c][:, j, :].ravel()))
                for i in self.anchor[c][j]:
                    lists[int(i)] = ordinary.copy()
                if j in d.markers:
                    L0, p = d.markers[j]
                    i = int(self.anchor[c][j, 0])
                    special[j] = i
                    lists[i] = ordinary - set(map(int, self.private[c][L0, j]))
                    lists[i].add(int(self.points[c][p]))
            self.special.append(special)
            self.anchor_lists.append(lists)
            poslists = []
            for z in range(d.r):
                j = d.pi(z)
                if z in d.markers:
                    poslists.append(lists[special[j]])
                else:
                    i = int(self.anchor[c][j, -1])
                    assert i != special.get(j)
                    poslists.append(lists[i])
            self.position_lists.append(poslists)
            loads = Counter(v for L in lists.values() for v in L)
            for i, L in lists.items():
                for v in L:
                    self.set_block(i, v, ((sigma, -sigma), (sigma, -sigma)), "list")
            for v, f in loads.items():
                assert f <= d.u
                for free in self.free[:f]:
                    self.set_block(v, int(free), ((-sigma, -sigma), (sigma, sigma)), "repair")
            for j, j2 in edges(d.a):
                for i, i2 in product(self.anchor[c][j], self.anchor[c][j2]):
                    self.checker(int(i), int(i2), sigma, "boundary")
                for L, L2 in product(range(d.b), repeat=2):
                    s = sigma if L == L2 else -sigma
                    for v, v2 in product(self.private[c][L, j], self.private[c][L2, j2]):
                        self.checker(int(v), int(v2), s, "private")
            for p in range(d.p):
                v = int(self.points[c][p])
                for L in range(d.b):
                    for j in range(d.m):
                        allowed = p in d.lines[L] and (j ^ d.alpha[L, p]).bit_count() == 1
                        s = sigma if allowed else -sigma
                        for v2 in self.private[c][L, j]:
                            self.checker(v, int(v2), s, "point")
        self.verify_host()

    def set_block(self, i, j, block, kind):
        assert i != j
        key = tuple(sorted((i, j)))
        assert key not in self.used, (key, kind, self.used.get(key))
        self.used[key] = kind
        for x in range(2):
            for y in range(2):
                self.S[2*i+x, 2*j+y] = block[x][y]
                self.S[2*j+y, 2*i+x] = block[x][y]

    def checker(self, i, j, s, kind):
        self.set_block(i, j, ((s, -s), (-s, s)), kind)

    def verify_host(self):
        assert np.array_equal(self.S, self.S.T)
        assert np.all(np.diag(self.S) == 0)
        assert np.count_nonzero(self.S) == self.N*(self.N-1)
        assert not np.any(self.S.sum(axis=1))
        assert np.all((self.S == 1).sum(axis=1) == (self.N-1)//2)
        assert np.all((self.S == -1).sum(axis=1) == (self.N-1)//2)
        change = self.S.astype(np.int16)-self.S0
        frobenius_sq = int(np.sum(change.astype(np.int64)**2))
        assert frobenius_sq <= 32*len(self.used)
        d = self.data
        for c, sigma in enumerate(self.sigma):
            boundary_pairs = self.anchor[c].ravel()
            available = np.ones(self.N, dtype=bool)
            available[2*boundary_pairs] = False
            available[2*boundary_pairs+1] = False
            for j in range(d.m):
                ordinary = [int(i) for i in self.anchor[c][j] if int(i) != self.special[c].get(j)]
                for ip, im in product(ordinary, repeat=2):
                    actual = set(np.flatnonzero((self.S[2*ip] == sigma)
                                                 & (self.S[2*im+1] == sigma) & available))
                    intended = {2*v for v in self.anchor_lists[c][ip]}
                    assert actual == intended, (c, j, ip, im, actual ^ intended)
                if j in self.special[c]:
                    i = self.special[c][j]
                    actual = set(np.flatnonzero((self.S[2*i] == sigma)
                                                 & (self.S[2*i+1] == sigma) & available))
                    assert actual == {2*v for v in self.anchor_lists[c][i]}
            # Every remaining colour edge used within a phase is present,
            # for all candidates, not only for one representative assignment.
            for L in range(d.b):
                for z, z2 in edges(d.k):
                    X = self.phase_choices(c, L, z)
                    Y = self.phase_choices(c, L, z2)
                    assert np.all(self.S[np.ix_(X, Y)] == sigma)

    def phase_choices(self, c, L, z):
        d = self.data
        if z in d.markers and d.markers[z][0] == L:
            return [2*int(self.points[c][d.markers[z][1]])]
        return list(2*self.private[c][L, d.pi(z)])

    def sample_boundary(self, c, rng):
        d = self.data
        plus, minus = {}, {}
        for j, fibre in enumerate(d.fibres):
            ordinary = [z for z in fibre if z not in d.markers]
            indices = [int(i) for i in self.anchor[c][j] if int(i) != self.special[c].get(j)]
            first, second = indices.copy(), indices.copy()
            rng.shuffle(first)
            rng.shuffle(second)
            for z, i, i2 in zip(ordinary, first, second):
                plus[z], minus[z] = 2*i, 2*i2+1
            if j in self.special[c]:
                plus[j], minus[j] = 2*self.special[c][j], 2*self.special[c][j]+1
        assert len(set(plus.values()) | set(minus.values())) == 2*d.r
        return plus, minus

    def sample_half(self, c, L, rng):
        d = self.data
        out = {}
        for j, fibre in enumerate(d.fibres):
            private_positions = []
            for z in fibre:
                if z in d.markers and d.markers[z][0] == L:
                    out[z] = 2*int(self.points[c][d.markers[z][1]])
                else:
                    private_positions.append(z)
            vals = list(map(int, 2*self.private[c][L, j]))
            rng.shuffle(vals)
            out.update(zip(private_positions, vals))
        assert len(set(out.values())) == d.r
        return out

    def check_sample_full_maps(self):
        d = self.data
        rng = random.Random(181)
        for c, sigma in enumerate(self.sigma):
            for _ in range(12):
                f0, f3 = self.sample_boundary(c, rng)
                if d.b > 1:
                    L, L2 = rng.sample(range(d.b), 2)
                    f1, f2 = self.sample_half(c, L, rng), self.sample_half(c, L2, rng)
                else:
                    # Disjoint private choices; the only collision is the point.
                    f1, f2 = {}, {}
                    for j, fibre in enumerate(d.fibres):
                        priv = []
                        for z in fibre:
                            if z in d.markers:
                                p = d.markers[z][1]
                                f1[z] = f2[z] = 2*int(self.points[c][p])
                            else:
                                priv.append(z)
                        vals = list(map(int, 2*self.private[c][0, j]))
                        rng.shuffle(vals)
                        f1.update(zip(priv, vals[:len(priv)]))
                        f2.update(zip(priv, vals[len(priv):2*len(priv)]))
                full = {}
                for prefix, f in enumerate((f0, f1, f2, f3)):
                    full.update({prefix*d.r+z: v for z, v in f.items()})
                assert len(full) == 4*d.r
                assert len(set(full.values())) == 4*d.r-1
                assert all(self.S[full[x], full[y]] == sigma for x, y in edges(d.k+2))
                collisions = [vs for vs in self.inverse(full).values() if len(vs) > 1]
                assert len(collisions) == 1 and len(collisions[0]) == 2
                x, y = collisions[0]
                if d.b > 1:
                    assert (x ^ y).bit_count() >= 4
                    assert not (set(neighbours(x, d.k+2)) & set(neighbours(y, d.k+2)))

    @staticmethod
    def inverse(f):
        out = {}
        for z, v in f.items():
            out.setdefault(v, []).append(z)
        return out


def check_small_image_count(host):
    d = host.data
    assert d.b == 1 and d.r == 8
    ZL, gamma = d.check_phase_lemma()
    counts = [d.u-1 if j in d.markers else d.u for j in range(d.m)]
    image_count = 1
    weight = 1
    for t in counts:
        image_count *= comb(2*d.u, t)
        weight *= factorial(t)
    assert image_count*weight == ZL
    for c in range(2):
        images = []
        pools = [list(map(int, 2*host.private[c][0, j])) for j in range(d.m)]
        point = 2*int(host.points[c][0])
        for choices in product(*(combinations(pool, t) for pool, t in zip(pools, counts))):
            image = frozenset([point] + [v for part in choices for v in part])
            assert len(image) == d.r and point in image
            images.append(image)
        assert len(set(images)) == image_count
    assert gamma == 20736
    assert ZL == 564480
    assert factorial(2*d.u)**d.m // 2 == 812851200
    print(f"  exact one-phase image count: {image_count} images, weight {weight}, Z={ZL}, Gamma={gamma}")


def check_spectra():
    for M, r in ((6, 2), (8, 3), (7, 3)):
        subsets = list(combinations(range(M), r))
        sets = list(map(set, subsets))
        K = np.array([[int(not x.intersection(y)) for y in sets] for x in sets], dtype=float)
        vals, vecs = np.linalg.eigh(K)
        expected = []
        for j in range(r+1):
            lam = (-1)**j * comb(M-r-j, r-j)
            multiplicity = comb(M, j) - (comb(M, j-1) if j else 0)
            expected += [lam]*multiplicity
        assert np.allclose(vals, sorted(expected), atol=1e-8)
        w = np.array([float(0 in s) for s in sets])
        Z = int(w.sum())
        D, L = comb(M-r, r), comb(M, r)
        assert w @ K @ w == 0
        coeff = vecs.T @ w
        negative = sum(-v*c*c for v, c in zip(vals, coeff) if v < -1e-8)
        assert abs(negative - D*Z*Z/L) < 1e-7
        if M == 7:
            lines = set(fano_lines())
            w = np.array([float(tuple(s) in lines) for s in subsets])
            assert int(w.sum()) == 7 and w @ K @ w == 0
            assert all(sum(w[i] for i, s in enumerate(sets) if x in s) == 3 for x in range(7))
            coeff = vecs.T @ w
            negative = sum(-v*c*c for v, c in zip(vals, coeff) if v < -1e-8)
            assert abs(negative - D*49/L) < 1e-7
    print("PASS Kneser eigenvalues, counting normalization, star and Fano zero-disjointness cases")


def check_signed_identities():
    for N in (5, 9):
        S = [[0 if x == y else (1 if (x-y) % N in ({1, N-1} if N == 5 else {1, 2, N-1, N-2}) else -1)
              for y in range(N)] for x in range(N)]
        assert all(sum(row) == 0 for row in S)
        @lru_cache(None)
        def J(v, E):
            total = 0
            for f in permutations(range(N), v):
                value = 1
                for x, y in E:
                    value *= S[f[x]][f[y]]
                total += value
            return total
        def canon(E):
            return tuple(sorted(tuple(sorted(e)) for e in E))
        for v in range(4):
            pairs = list(combinations(range(v), 2))
            for mask in range(1 << len(pairs)):
                E = {e for i, e in enumerate(pairs) if mask >> i & 1}
                left = J(v+2, canon(E | {(v, v+1)}))
                right = 2*sum(J(v, canon(E ^ {ab})) for ab in pairs)
                assert left == right, (N, v, E, left, right)
        for v in range(2, 5):
            pairs = list(combinations(range(v), 2))
            for mask in range(1 << len(pairs)):
                E = {e for i, e in enumerate(pairs) if mask >> i & 1}
                degrees = Counter(x for e in E for x in e)
                for z in range(v):
                    if degrees[z] != 1:
                        continue
                    u = next(y if x == z else x for x, y in E if z in (x, y))
                    vertices = [x for x in range(v) if x != z]
                    rename = {x: i for i, x in enumerate(vertices)}
                    core = {e for e in E if z not in e}
                    right = 0
                    for x in vertices:
                        if x == u:
                            continue
                        toggled = core ^ {tuple(sorted((u, x)))}
                        right -= J(v-1, canon((rename[a], rename[b]) for a, b in toggled))
                    assert J(v, canon(E)) == right
        assert Fraction(J(3, ((0, 1), (1, 2))), falling(N, 3)) == -Fraction(1, N-2)
        assert Fraction(J(4, ((0, 1), (2, 3))), falling(N, 4)) == Fraction(2, (N-2)*(N-3))
    print("PASS deterministic isolated-edge and leaf cancellation, all graphs through four vertices")


def check_asymptotics():
    mp.mp.dps = 75
    q, C = 2, 16
    b, ell = q*q+q+1, q+1
    DD = b*ell
    print("High-precision (log negative-lower-bound / baseline)/(h log h), q=2, C=16:")
    last = None
    for a in (6, 20, 80, 320, 1280):
        m, u, r = 1 << a, 1 << (2*a), 1 << (3*a)
        h, N = 4*r, 4*C*r+1
        M = N-2*r
        def logfall(x, t):
            return mp.loggamma(mp.mpf(x)+1)-mp.loggamma(mp.mpf(x-t)+1)
        logp = logfall(M-r, r)-logfall(M, r)
        logbase = logfall(N, h)+(1-(3*a+2)*2*r)*mp.log(2)
        logneg = (mp.log(2)+logp+2*mp.log(b)+2*m*mp.loggamma(mp.mpf(2*u)+1)
                  -2*DD*mp.log(u)-2*ell*mp.log(u+1))
        ratio = (logneg-logbase)/(h*mp.log(h))
        if last is not None:
            assert ratio > last
        last = ratio
        print(f"  a={a:4d}: {mp.nstr(ratio, 14)}")
    assert abs(last-mp.mpf(1)/6) < mp.mpf("0.002")
    print("PASS factorial asymptotics approach the proved coefficient 1/6")


def main():
    assert hashlib.sha256((ROOT / "Spec.lean").read_bytes()).hexdigest() == SPEC_HASH
    check_spectra()
    for label, a, k, lines, C in (
        ("single point", 1, 3, ((0,),), 4),
        ("triangle phases", 4, 6, ((0, 1), (0, 2), (1, 2)), 8),
    ):
        d = Data(a, k, lines)
        d.check_phase_lemma()
        host = Host(d, C)
        host.check_sample_full_maps()
        if d.b == 1:
            check_small_image_count(host)
        counts = dict(sorted(Counter(host.used.values()).items()))
        print(f"PASS {label}: N={host.N}, d={k+2}, exact regularity, exact lists, all phase edges, one-collision maps")
        print(f"  modified pair blocks: {counts}")
    fano = Data(6, 8, fano_lines())
    fano.check_phase_lemma()
    assert Fraction(fano.ell, fano.b) == Fraction(3, 7)
    assert Fraction(fano.b-1, fano.b) == Fraction(6, 7)
    print("PASS Fano incidence, quotient, marker separation, phase rigidity, exact factorial counts and occupancies")
    check_signed_identities()
    check_asymptotics()
    assert hashlib.sha256((ROOT / "Spec.lean").read_bytes()).hexdigest() == SPEC_HASH
    print("PASS Spec.lean unchanged; all checks completed")


if __name__ == "__main__":
    main()
