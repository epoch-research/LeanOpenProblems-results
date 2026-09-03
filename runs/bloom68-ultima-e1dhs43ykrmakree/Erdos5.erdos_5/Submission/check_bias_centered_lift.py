#!/usr/bin/env python3
"""Exact finite checks for BiasCenteredLiftAttempt.md; no asymptotic claims."""
from fractions import Fraction as Q
from itertools import combinations
from math import gcd, prod

LIMIT = 6000
spf = list(range(LIMIT + 1))
for p in range(2, int(LIMIT ** 0.5) + 1):
    if spf[p] == p:
        for n in range(p * p, LIMIT + 1, p):
            if spf[n] == n:
                spf[n] = p


def factor(n):
    out = {}
    while n > 1:
        p = spf[n]
        out[p] = out.get(p, 0) + 1
        n //= p
    return out


def omega(n):
    return sum(factor(n).values())


def lam(n):
    return (-1) ** omega(n)


def prime(n):
    return n > 1 and spf[n] == n


def sr(n, y):
    s = prod(p ** a for p, a in factor(n).items() if p <= y)
    return s, n // s


def S(n, y):
    return lam(sr(n, y)[0])


def Z(n, y):
    return lam(n) if sr(n, y)[1] == 1 else 0


def F(n, y):
    s, r = sr(n, y)
    return lam(s) * int(prime(r))


def G(n, y, rho):
    s, r = sr(n, y)
    return lam(s) * (int(prime(r)) - rho * int(r > 1))


def odd_tail(n, y):
    r = sr(n, y)[1]
    o = omega(r)
    return int(o >= 3 and o % 2 == 1)


def R(n, y):
    return n > 1 and sr(n, y)[0] == 1


def c(n, labels):
    return prod(Q(int(n % p == 0)) - Q(1, p) for p in labels)


rho = Q(7, 11)
identity_checks = 0
for y in (3, 5, 7, 11):
    for n in range(1, LIMIT + 1):
        s, r = sr(n, y)
        tail = S(n, y) * odd_tail(n, y)
        assert F(n, y) == (Q(S(n, y)) - lam(n)) / 2 - tail
        assert G(n, y, rho) == (Q(1, 2) - rho) * S(n, y) - Q(lam(n), 2) + rho * Z(n, y) - tail
        uncut = lam(s) * (int(prime(r)) - rho)
        assert uncut == (Q(1, 2) - rho) * S(n, y) - Q(lam(n), 2) - tail
        # The two-term identity needs no correction at r=1 for the *uncut* lift.
        if r == 1:
            assert uncut == -rho * lam(n) and G(n, y, rho) == 0
        if n < y ** 3:
            assert odd_tail(n, y) == 0
        if n > 1 and sr(n, y)[0] == 1:
            assert G(n, y, rho) == int(prime(n)) - rho
        identity_checks += 1

multiplicativity_checks = 0
for y in (5, 11):
    for a in range(1, 61):
        for b in range(1, 61):
            assert S(a * b, y) == S(a, y) * S(b, y)
            assert lam(a * b) == lam(a) * lam(b)
            assert Z(a * b, y) == Z(a, y) * Z(b, y)
            multiplicativity_checks += 1

# Full centered displacement transport and its real-multiplicative decomposition.
y = 7
pool = (3, 5, 7)
anchors = {11, 13, 23}
V = set(range(25, 301)) - {37, 55, 103, 169, 231}
FA = lambda n: S(n, y) * int(sr(n, y)[1] in anchors)
g = lambda n: G(n, y, rho)
transport_checks = 0
pinching_checks = 0
remainder_checks = 0
nonzero_remainders = 0
for k in (1, 2, 3):
    label_sets = list(combinations(pool, k))
    products = {prod(ps) for ps in label_sets}
    for h in (2, 4):
        assert all(gcd(h, p) == 1 for p in pool)
        for sign in (-1, 1):
            def bilinear(right, pinch=False):
                ans = Q(0)
                for ps in label_sets:
                    m = prod(ps)
                    for n in V:
                        v = n + sign * h * m
                        if v not in V:
                            continue
                        if pinch:
                            sn, sv = sr(n, y)[0], sr(v, y)[0]
                            if sn != sv or sn not in products:
                                continue
                        ans += FA(n) * c(n, ps) * right(v)
                return ans

            direct = bilinear(g)
            decomp = (Q(1, 2) - rho) * bilinear(lambda n: S(n, y)) - Q(1, 2) * bilinear(lam) + rho * bilinear(lambda n: Z(n, y))
            assert direct == decomp  # Every endpoint is < y^3.
            transported = Q(0)
            for ps in label_sets:
                m = prod(ps)
                for j in range(k + 1):
                    for ds in combinations(ps, j):
                        d = prod(ds)
                        e = m // d
                        coeff = Q((-1) ** (k - j), e)
                        for u in range(1, max(V) // d + 1):
                            v = u + sign * h * e
                            if v > 0 and d * u in V and d * v in V:
                                transported += coeff * FA(u) * g(v)
            assert direct == transported
            transport_checks += 1

            local_main, remainder = Q(0), Q(0)
            kappa_budget = Q(0)
            for ps in label_sets:
                m = prod(ps)
                kappa = prod(-Q(4 * (p - 1), p * p * (p + 1)) for p in ps)
                kappa_budget += abs(kappa)
                for n in V:
                    v = n + sign * h * m
                    if v not in V:
                        continue
                    # U_m(n)U_m(v), with every label valuation retained.
                    phase = (-1) ** sum(factor(n).get(p, 0) + factor(v).get(p, 0) for p in ps)
                    external = phase * FA(n) * g(v)
                    K = c(n, ps) * phase
                    local_main += kappa * external
                    remainder += (K - kappa) * external
            assert direct == local_main + remainder
            assert abs(local_main) <= len(V) * kappa_budget
            assert kappa_budget <= Q(4, min(pool)) ** k * sum(Q(1, m) for m in products)
            remainder_checks += 1
            nonzero_remainders += int(remainder != 0)

            pinched = bilinear(g, pinch=True)
            blocks = Q(0)
            for ps in label_sets:
                m = prod(ps)
                weight = prod(Q(p - 1, p) for p in ps)
                for p in anchors:
                    q = p + sign * h
                    if q > 1 and m * p in V and m * q in V and R(q, y):
                        blocks += weight * (int(prime(q)) - rho)
            assert pinched == blocks
            pinching_checks += 1

# Haar local calculations are exact already modulo p^2 if the zero residue
# is assigned its conditional mean E[(-1)^v | p^2 divides n]=(p-1)/(p+1).
def local_phase_mean(n, p):
    n %= p * p
    if n == 0:
        return Q(p - 1, p + 1)
    return Q(-1 if n % p == 0 else 1)


local_checks = 0
for p in (2, 3, 5, 7, 11, 13):
    for u in range(1, 2 * p):
        if u % p == 0:
            continue
        shift = p * u
        corr = Q(0)
        centered = Q(0)
        for n in range(p * p):
            ph = local_phase_mean(n, p) * local_phase_mean(n + shift, p)
            corr += ph
            centered += (Q(int(n % p == 0)) - Q(1, p)) * ph
        corr /= p * p
        centered /= p * p
        assert corr == 1 - Q(4, p * (p + 1))
        assert centered == -Q(4 * (p - 1), p * p * (p + 1))
        local_checks += 1

crt_checks = 0
for ps in ((3, 5), (3, 7), (3, 5, 7)):
    m = prod(ps)
    modulus = m * m
    shift = 2 * m
    total = Q(0)
    for n in range(modulus):
        phase = prod(local_phase_mean(n, p) * local_phase_mean(n + shift, p) for p in ps)
        total += c(n, ps) * phase
    total /= modulus
    expected = prod(-Q(4 * (p - 1), p * p * (p + 1)) for p in ps)
    assert total == expected
    crt_checks += 1

# A finite interval with an actual missing band; this checks geometry only.
# On primes 100 < p <= 130, no gap lies in (6.5,9.5).  The anchor is 113,
# and 113+8=121 supplies a nonzero rough-composite mass.
primes = [n for n in range(2, LIMIT + 1) if prime(n)]
next_prime = {p: q for p, q in zip(primes, primes[1:])}
lo, hi = Q(13, 2), Q(19, 2)
Hs = range(7, 10)
base = [p for p in primes if 100 < p <= 140 - hi]
assert all(not (lo < next_prime[p] - p < hi) for p in base)
E = {p for p in base if next_prime[p] - p > lo}
assert E == {113}
mask_checks = 0
for p in base:
    for h in Hs:
        interior = all(not prime(p + j) for j in range(1, h))
        assert interior == (p in E)
        if p in E:
            assert not prime(p + h)
        mask_checks += 1
mass = sum(int(R(p + h, y)) for p in E for h in Hs)
centered = sum((int(prime(p + h)) - rho * int(R(p + h, y))) for p in E for h in Hs)
assert mass == 1 and centered == -rho * mass

print(f"PASS: {identity_checks} full lift identities (including r=1 and odd Omega>=3)")
print(f"PASS: {multiplicativity_checks} complete-multiplicativity checks")
print(f"PASS: {transport_checks} masked real-phase transports; {pinching_checks} exact top blocks")
print(f"PASS: {remainder_checks} exact local-mean/remainder splits and budgets ({nonzero_remainders} nonzero remainders)")
print(f"PASS: {local_checks} local parity covariances; {crt_checks} composite CRT products")
print(f"PASS: {mask_checks} common-anchor masks; nonzero centered composite mass {centered}")
