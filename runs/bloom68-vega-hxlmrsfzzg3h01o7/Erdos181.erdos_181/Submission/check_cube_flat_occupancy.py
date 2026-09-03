#!/usr/bin/env python3
"""Checks for the tagged, O(r/M)-occupancy refinement in Section 11."""
from collections import Counter, deque, defaultdict
from fractions import Fraction
from itertools import product, permutations
from math import factorial
import hashlib
import random

import numpy as np
import mpmath as mp

from check_cube_finite_population_reflection import (
    Host, edges, neighbours, falling, fano_lines, ROOT, SPEC_HASH,
)


class TaggedData:
    def __init__(self, a, k, lines):
        self.a, self.k = a, k
        self.m, self.u, self.r = 1 << a, 1 << (k-a), 1 << k
        self.lines = tuple(tuple(L) for L in lines)
        self.b = len(lines)
        self.ell = self.s = len(lines[0])
        self.p = max(max(L) for L in lines)+1
        self.D = self.b*self.ell
        self.t = (self.b-1).bit_length()
        self.tau = 1 << self.t
        assert a > self.t and self.u >= max(self.ell, 2)
        self.tag_cells = {j for j in range(self.m) if not j & (self.tau-1)}
        self.mT = len(self.tag_cells)
        self.ordinary_cells = set(range(self.m))-self.tag_cells
        available = [j for j in range(self.m)
                     if j & (self.tau-1) == 1 and not j.bit_count() % 2]
        assert len(available) >= self.D
        self.alpha, self.beta, self.markers = {}, {}, {}
        i = 0
        for L, line in enumerate(lines):
            for p in line:
                alpha = available[i]
                self.alpha[L, p], self.beta[L, p] = alpha, alpha ^ 1
                self.markers[alpha] = (L, p)
                i += 1
        self.fibres = [[z for z in range(self.r) if self.pi(z) == j]
                       for j in range(self.m)]
        assert all(len(f) == self.u for f in self.fibres)

    def pi(self, z):
        return (z & (self.m-1)) ^ (((z >> self.a).bit_count() % 2) << self.t)

    def is_tagged(self, z):
        return not z & (self.tau-1)

    def phase_type(self, L, z):
        if self.is_tagged(z):
            return ("U", L, self.pi(z))
        if z in self.markers:
            L0, p = self.markers[z]
            return ("P", p) if L == L0 else ("W", z)
        return ("V", self.pi(z))

    def capacity(self, pool):
        return {"U": 2*self.u, "V": self.s*self.u,
                "W": self.u, "P": 1}[pool[0]]

    def compatible(self, x, y):
        if x[0] == "U" and y[0] == "U":
            return x[1] == y[1] and (x[2] ^ y[2]).bit_count() == 1
        if x[0] == "V" and y[0] == "V":
            return (x[1] ^ y[1]).bit_count() == 1
        if x[0] == "V":
            x, y = y, x
        if x[0] == "U" and y[0] == "V":
            return (x[2] ^ y[1]).bit_count() == 1
        if x[0] in ("P", "W") and y[0] == "V":
            return True
        if x[0] == "U":
            x, y = y, x
        if x[0] == "W" and y[0] == "U":
            return self.markers[x[1]][0] != y[1]
        if x[0] == "P" and y[0] == "U":
            p, L, j = x[1], y[1], y[2]
            return p in self.lines[L] and j == self.beta[L, p]
        return False

    def check(self, C, occupancy_cap=True):
        d = self
        for x, y in edges(d.k):
            assert (d.pi(x) ^ d.pi(y)).bit_count() == 1
        tag = {z for z in range(d.r) if d.is_tagged(z)}
        assert len(tag) == d.r//d.tau
        visited = {0}
        queue = deque([0])
        while queue:
            for y in neighbours(queue.popleft(), d.k):
                if y in tag and y not in visited:
                    visited.add(y)
                    queue.append(y)
        assert visited == tag
        for z, (L0, p) in d.markers.items():
            assert z not in tag
            assert all(y not in d.markers for y in neighbours(z, d.k))
            tagged_neighbours = [y for y in neighbours(z, d.k) if y in tag]
            assert len(tagged_neighbours) == 1
            assert d.pi(tagged_neighbours[0]) == d.beta[L0, p]
            for L in range(d.b):
                choices = [("W", z), ("P", p)]
                good = [x for x in choices
                        if all(d.compatible(x, d.phase_type(L, y))
                               for y in neighbours(z, d.k))]
                assert good == [d.phase_type(L, z)]
        for L in range(d.b):
            assert all(d.compatible(d.phase_type(L, x), d.phase_type(L, y))
                       for x, y in edges(d.k))
        Z = (falling(2*d.u, d.u)**d.mT
             * falling(d.s*d.u, d.u)**(d.m-d.mT-d.D)
             * falling(d.s*d.u, d.u-1)**d.D * d.u**(d.D-d.ell))
        Y = (falling(2*d.u, d.u)**(2*d.mT)
             * falling(d.s*d.u, 2*d.u)**(d.m-d.mT-d.D)
             * falling(d.s*d.u, 2*d.u-2)**d.D
             * d.u**(2*d.ell) * (d.u*(d.u-1))**(d.D-2*d.ell))
        phase_counts = []
        for L in range(d.b):
            loads = Counter(d.phase_type(L, z) for z in range(d.r))
            value = 1
            for pool, load in loads.items():
                value *= falling(d.capacity(pool), load)
            assert value == Z
            phase_counts.append(loads)
        for L, L2 in permutations(range(d.b), 2):
            loads = phase_counts[L]+phase_counts[L2]
            value, double_points = 1, []
            for pool, load in loads.items():
                if pool[0] == "P":
                    assert load in (1, 2)
                    if load == 2:
                        double_points.append(pool[1])
                else:
                    value *= falling(d.capacity(pool), load)
            assert len(double_points) == 1 and value == Y
            p, = double_points
            assert 2+(d.alpha[L, p] ^ d.alpha[L2, p]).bit_count() >= 4
        M = (4*C-2)*d.r+1
        marginals = (Fraction(d.ell, d.b), Fraction(1, 2*d.b),
                     Fraction(1, d.s), Fraction(d.b-1, d.b*d.u))
        if occupancy_cap:
            assert max(marginals) == Fraction(d.ell, d.b)
            assert max(marginals) <= Fraction(12*d.r, M)
        # Sum of all conditional occupancy probabilities must be exactly r.
        total = (d.p*Fraction(d.ell, d.b)
                 + d.b*d.mT*2*d.u*Fraction(1, 2*d.b)
                 + (d.m-d.mT-d.D)*d.s*d.u*Fraction(1, d.s)
                 + d.D*d.s*d.u*Fraction(d.u-1, d.s*d.u)
                 + d.D*d.u*Fraction(d.b-1, d.b*d.u))
        assert total == d.r
        n_main = 2*(d.r+2*d.b*d.r//d.tau
                    + d.s*(d.r-d.r//d.tau)+d.D*d.u)
        extra = ((2*d.p+d.u-1)//d.u)*d.u+d.u
        assert n_main+extra <= 2*C*d.r
        return Z, Y


def paired_initial(n, u, anchors):
    groups = np.arange(n)//u
    T = 1 << ((int(groups[-1])+1)-1).bit_length()
    H = np.array([[1 if (x & y).bit_count() % 2 == 0 else -1
                   for y in range(T)] for x in range(T)], dtype=np.int8)
    W = H[groups[:, None], groups[None, :]].copy()
    np.fill_diagonal(W, 0)
    S = np.zeros((2*n+1, 2*n+1), dtype=np.int8)
    S[0:2*n:2, 0:2*n:2] = W
    S[0:2*n:2, 1:2*n:2] = -W
    S[1:2*n:2, 0:2*n:2] = -W
    S[1:2*n:2, 1:2*n:2] = W
    t = np.zeros(n, dtype=np.int8)
    t[anchors[0].ravel()] = 1
    t[anchors[1].ravel()] = -1
    rest = np.flatnonzero(t == 0)
    assert len(rest) % 2 == 0
    t[rest[:len(rest)//2]] = 1
    t[rest[len(rest)//2:]] = -1
    assert not t.sum()
    for i in range(n):
        S[2*i, 2*i+1] = S[2*i+1, 2*i] = t[i]
        S[2*i, -1] = S[-1, 2*i] = -t[i]
        S[2*i+1, -1] = S[-1, 2*i+1] = -t[i]
    assert not np.any(S.sum(axis=1))
    return S, T


class TaggedHost(Host):
    def __init__(self, d, C):
        self.data = d
        self.n = 2*C*d.r
        self.N = 2*self.n+1
        self.sigma = (1, -1)
        self.anchor, self.pools = [], []
        pos = 0
        for c in range(2):
            self.anchor.append(np.arange(pos, pos+d.r).reshape(d.m, d.u))
            pos += d.r
            pools = {}
            for L in range(d.b):
                for j in sorted(d.tag_cells):
                    pools["U", L, j] = np.arange(pos, pos+2*d.u)
                    pos += 2*d.u
            for j in sorted(d.ordinary_cells):
                pools["V", j] = np.arange(pos, pos+d.s*d.u)
                pos += d.s*d.u
            for z in d.markers:
                pools["W", z] = np.arange(pos, pos+d.u)
                pos += d.u
            self.pools.append(pools)
        self.points = [np.arange(pos+c*d.p, pos+(c+1)*d.p) for c in range(2)]
        for c in range(2):
            for p in range(d.p):
                self.pools[c]["P", p] = self.points[c][p:p+1]
        pos += ((2*d.p+d.u-1)//d.u)*d.u
        self.free = np.arange(pos, pos+d.u)
        pos += d.u
        assert pos <= self.n
        self.padding_start = pos
        self.S, self.T = paired_initial(self.n, d.u, self.anchor)
        self.S0 = self.S.copy()
        self.used = {}
        self.special, self.anchor_lists, self.position_lists = [], [], []
        for c, sigma in enumerate(self.sigma):
            pools = self.pools[c]
            lists, special = {}, {}
            for j in range(d.m):
                ordinary = (set(int(v) for L in range(d.b) for v in pools["U", L, j])
                            if j in d.tag_cells else set(map(int, pools["V", j])))
                for i in self.anchor[c][j]:
                    lists[int(i)] = ordinary.copy()
                if j in d.markers:
                    L0, p = d.markers[j]
                    i = int(self.anchor[c][j, 0])
                    special[j] = i
                    lists[i] = set(map(int, pools["W", j])) | {int(self.points[c][p])}
            self.special.append(special)
            self.anchor_lists.append(lists)
            poslists = []
            for z in range(d.r):
                j = d.pi(z)
                poslists.append(lists[special[j]] if z in d.markers
                                else lists[int(self.anchor[c][j, -1])])
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
                if j in d.tag_cells and j2 in d.tag_cells:
                    for L, L2 in product(range(d.b), repeat=2):
                        self.force_pools(c, ("U", L, j), ("U", L2, j2),
                                         sigma if L == L2 else -sigma, "tagged")
                elif j not in d.tag_cells and j2 not in d.tag_cells:
                    self.force_pools(c, ("V", j), ("V", j2), sigma, "ordinary")
                else:
                    if j2 in d.tag_cells:
                        j, j2 = j2, j
                    for L in range(d.b):
                        self.force_pools(c, ("U", L, j), ("V", j2), sigma, "interface")
            for z, (L0, p) in d.markers.items():
                for L in range(d.b):
                    for j in d.tag_cells:
                        self.force_pools(c, ("W", z), ("U", L, j),
                                         sigma if L != L0 else -sigma, "replacement-tag")
                for j in d.ordinary_cells:
                    self.force_pools(c, ("W", z), ("V", j), sigma, "replacement-ordinary")
            for p in range(d.p):
                for L in range(d.b):
                    for j in d.tag_cells:
                        allowed = p in d.lines[L] and j == d.beta[L, p]
                        self.force_pools(c, ("P", p), ("U", L, j),
                                         sigma if allowed else -sigma, "point-tag")
                for j in d.ordinary_cells:
                    self.force_pools(c, ("P", p), ("V", j), sigma, "point-ordinary")
        self.verify_host()  # inherited exact degree/list/all-phase-edge checks

    def force_pools(self, c, p, p2, sign, kind):
        for v, v2 in product(self.pools[c][p], self.pools[c][p2]):
            self.checker(int(v), int(v2), sign, kind)

    def phase_choices(self, c, L, z):
        return list(2*self.pools[c][self.data.phase_type(L, z)])

    def plant_red_witness(self):
        d = self.data
        witness = list(range(self.padding_start, self.padding_start+2*d.r))
        assert witness[-1] < self.n
        boundary = set(map(int, np.concatenate([a.ravel() for a in self.anchor])))
        targets = [i for i in witness if self.S[2*i, 2*i+1] == -1]
        forbidden = boundary | set(witness)
        donors = [i for i in range(self.n) if i not in forbidden
                  and self.S[2*i, 2*i+1] == 1]
        assert len(donors) >= len(targets)
        for i, donor in zip(targets, donors):
            for index, sign in ((i, 1), (donor, -1)):
                for matrix in (self.S, self.S0):
                    matrix[2*index, 2*index+1] = matrix[2*index+1, 2*index] = sign
                    matrix[2*index, -1] = matrix[-1, 2*index] = -sign
                    matrix[2*index+1, -1] = matrix[-1, 2*index+1] = -sign
        for x, y in edges(d.k+1):
            self.checker(witness[x], witness[y], 1, "red-witness")
        f = {z: 2*witness[z % (2*d.r)]+z//(2*d.r) for z in range(4*d.r)}
        assert len(set(f.values())) == 4*d.r
        assert all(self.S[f[x], f[y]] == 1 for x, y in edges(d.k+2))
        self.verify_host()
        trimmed = self.S[:-1, :-1]
        assert Counter(map(int, (trimmed == 1).sum(axis=1))) == {self.n: self.n, self.n-1: self.n}
        assert Counter(map(int, (trimmed == -1).sum(axis=1))) == {self.n: self.n, self.n-1: self.n}

    def check_full_maps(self):
        d = self.data
        rng = random.Random(18111)
        for c, sigma in enumerate(self.sigma):
            for L, L2 in permutations(range(d.b), 2):
                f0, f3 = self.sample_boundary(c, rng)
                f1, f2 = {}, {}
                by_pool = defaultdict(list)
                for side, phase in enumerate((L, L2)):
                    for z in range(d.r):
                        pool = d.phase_type(phase, z)
                        if pool[0] == "P":
                            (f1 if side == 0 else f2)[z] = 2*int(self.points[c][pool[1]])
                        else:
                            by_pool[pool].append((side, z))
                for pool, positions in by_pool.items():
                    values = list(map(int, 2*self.pools[c][pool]))
                    assert len(positions) <= len(values)
                    rng.shuffle(values)
                    for (side, z), value in zip(positions, values):
                        (f1 if side == 0 else f2)[z] = value
                full = {}
                for prefix, f in enumerate((f0, f1, f2, f3)):
                    full.update({prefix*d.r+z: value for z, value in f.items()})
                assert len(full) == 4*d.r
                assert len(set(full.values())) == 4*d.r-1
                assert all(self.S[full[x], full[y]] == sigma for x, y in edges(d.k+2))
                collision, = [xs for xs in self.inverse(full).values() if len(xs) == 2]
                assert (collision[0] ^ collision[1]).bit_count() >= 4


def check_asymptotic_refinement():
    mp.mp.dps = 70
    b, ell, s, C, tau = 7, 3, 3, 7, 8
    DD = b*ell
    print("Tagged refinement: normalized logarithmic excess (negative mass, one-collision maps):")
    last = None
    for a in (10, 40, 160, 640, 2560):
        m, u, r = 1 << a, 1 << (2*a), 1 << (3*a)
        mT, h, N = m//tau, 4*r, 4*C*r+1
        M = N-2*r
        def lf(x, k):
            return mp.loggamma(mp.mpf(x)+1)-mp.loggamma(mp.mpf(x-k)+1)
        logbase = lf(N, h)+(1-2*r*(3*a+2))*mp.log(2)
        logp = lf(M-r, r)-lf(M, r)
        loggamma = 2*m*mp.loggamma(mp.mpf(u)+1)-2*DD*mp.log(u)
        logZ = (mT*lf(2*u, u)+(m-mT-DD)*lf(s*u, u)
                +DD*lf(s*u, u-1)+(DD-ell)*mp.log(u))
        logY = (2*mT*lf(2*u, u)+(m-mT-DD)*lf(s*u, 2*u)
                +DD*lf(s*u, 2*u-2)+2*ell*mp.log(u)
                +(DD-2*ell)*(mp.log(u)+mp.log(u-1)))
        logneg = mp.log(2)+logp+loggamma+2*mp.log(b)+2*logZ
        logone = mp.log(2)+loggamma+mp.log(b*(b-1))+logY
        ratios = ((logneg-logbase)/(h*mp.log(h)), (logone-logbase)/(h*mp.log(h)))
        if last is not None:
            assert all(x > y for x, y in zip(ratios, last))
        last = ratios
        print(f"  a={a:4d}: {mp.nstr(ratios[0], 13)}, {mp.nstr(ratios[1], 13)}")
    assert all(abs(x-mp.mpf(1)/6) < mp.mpf("0.002") for x in last)
    # Independent first-order Stirling constants, including log r = log h-log 4.
    f = lambda x: mp.mpf(x)*mp.log(x)
    base_constant = f(4*C)-f(4*C-4)-4-4*mp.log(2)
    p_constant = 2*f(4*C-3)-f(4*C-4)-f(4*C-2)
    g2 = f(2)-f(1)-1
    gs = f(s)-f(s-1)-1
    gs2 = f(s)-f(s-2)-2
    Z_constant = g2/tau+gs*(1-mp.mpf(1)/tau)
    Y_constant = 2*g2/tau+gs2*(1-mp.mpf(1)/tau)
    constants = ((p_constant-2+2*Z_constant-base_constant)/4-mp.log(4)/6,
                 (-2+Y_constant-base_constant)/4-mp.log(4)/6)
    for ratio, constant in zip(last, constants):
        predicted = mp.mpf(1)/6+constant/((3*a+2)*mp.log(2))
        assert abs(ratio-predicted) < mp.mpf("1e-50")
    print("PASS tagged factorial exponents approach 1/6 and match independent Stirling constants")


def check_optimized_parameters():
    mp.mp.dps = 75
    b, ell, s, C, tau, DD = 7, 3, 3, 7, 8, 21
    print("Optimized a=2 log_2 k: normalized excesses approach 1/2:")
    last = None
    for k in (32, 128, 512, 2048, 8192):
        a = 2*(k.bit_length()-1)
        m, u, r = 1 << a, 1 << (k-a), 1 << k
        assert m == k*k and k >= a+2
        mT, h, N = m//tau, 4*r, 4*C*r+1
        M = N-2*r
        def lf(x, j):
            return mp.loggamma(mp.mpf(x)+1)-mp.loggamma(mp.mpf(x-j)+1)
        logbase = lf(N, h)+(1-2*r*(k+2))*mp.log(2)
        logp = lf(M-r, r)-lf(M, r)
        loggamma = 2*m*mp.loggamma(mp.mpf(u)+1)-2*DD*mp.log(u)
        logZ = (mT*lf(2*u, u)+(m-mT-DD)*lf(s*u, u)
                +DD*lf(s*u, u-1)+(DD-ell)*mp.log(u))
        logY = (2*mT*lf(2*u, u)+(m-mT-DD)*lf(s*u, 2*u)
                +DD*lf(s*u, 2*u-2)+2*ell*mp.log(u)
                +(DD-2*ell)*(mp.log(u)+mp.log(u-1)))
        logneg = mp.log(2)+logp+loggamma+2*mp.log(b)+2*logZ
        logone = mp.log(2)+loggamma+mp.log(b*(b-1))+logY
        excesses = ((logneg-logbase)/h, (logone-logbase)/h)
        ratios = tuple(x/mp.log(h) for x in excesses)
        residuals = tuple(x-mp.log(h)/2+2*mp.log(mp.log(h)) for x in excesses)
        assert all(-5 < x < -3 for x in residuals)
        if last is not None:
            assert all(x > y for x, y in zip(ratios, last))
        last = ratios
        print(f"  k={k:4d}, a={a:2d}: {mp.nstr(ratios[0], 13)}, {mp.nstr(ratios[1], 13)}")
    assert all(mp.mpf('0.495') < x < mp.mpf('0.5') for x in last)
    print("PASS optimized lower bounds: (h/2)log h-2h log log h-O(h)")


def main():
    assert hashlib.sha256((ROOT / "Spec.lean").read_bytes()).hexdigest() == SPEC_HASH
    triangle = TaggedData(6, 8, ((0, 1), (0, 2), (1, 2)))
    triangle.check(6, occupancy_cap=False)
    host = TaggedHost(triangle, 6)
    host.check_full_maps()
    host.plant_red_witness()
    host.check_full_maps()
    print(f"PASS tagged paired realization: N={host.N}, d={triangle.k+2}, two colours exactly regular")
    print("PASS explicit red cube in padding; bad families unchanged; apex deletion gives degrees N/2 and N/2-1")
    print("PASS exact common-neighbour lists, phase gating, disjoint-private one-collision maps")
    print("  modified pair blocks:", dict(sorted(Counter(host.used.values()).items())))
    fano = TaggedData(9, 11, fano_lines())
    fano.check(7)
    print("PASS Fano tagged source: connected phase subcube, marker gating, exact Z and Y counts")
    print("PASS Fano occupancies sum to r and maximum is <=12r/M; construction fits N=7h+1")
    for q in (2, 3, 4, 5, 7, 8, 9, 16, 32, 64, 128):
        b, ell = q*q+q+1, q+1
        assert Fraction((4*q+19)*ell, b) <= 12
        if q >= 8 and q & (q-1) == 0:
            assert Fraction((8*q+19)*ell, b) <= 12
    print("PASS uniform occupancy-cap inequality, including padding for every fixed C>=13")
    check_asymptotic_refinement()
    check_optimized_parameters()
    assert hashlib.sha256((ROOT / "Spec.lean").read_bytes()).hexdigest() == SPEC_HASH
    print("PASS Spec.lean unchanged; all refinement checks completed")


if __name__ == "__main__":
    main()
