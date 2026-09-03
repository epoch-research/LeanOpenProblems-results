#!/usr/bin/env python3
"""Independent finite/symbolic checks for MiddleDivisorDetectorAudit.md.

This is evidence for the elementary identities, not a prime-correlation theorem.
Spec.lean is neither imported nor used.
"""
from fractions import Fraction
from itertools import product
from math import exp, gcd, isqrt, lcm, log, sqrt, atanh
import argparse

import numpy as np
from scipy.integrate import quad
import sympy as sp


def arithmetic_tables(limit):
    spf = list(range(limit + 1))
    for p in range(2, isqrt(limit) + 1):
        if spf[p] == p:
            for n in range(p * p, limit + 1, p):
                if spf[n] == n:
                    spf[n] = p
    mu = [0] * (limit + 1)
    mu[1] = 1
    for n in range(2, limit + 1):
        p = spf[n]
        m = n // p
        mu[n] = 0 if m % p == 0 else -mu[m]
    return spf, mu


def factor(n, spf):
    result = []
    while n > 1:
        p = spf[n]
        a = 0
        while n % p == 0:
            n //= p
            a += 1
        result.append((p, a))
    return result


def divisors(factors):
    ds = [1]
    for p, a in factors:
        ds = [d * p ** j for d in ds for j in range(a + 1)]
    return sorted(ds)


def step(u):
    """A C-infinity step, zero for u <= 0 and one for u >= 1."""
    if u <= 0:
        return 0.0
    if u >= 1:
        return 1.0
    z = -1 / u + 1 / (1 - u)
    if z >= 0:
        return 1 / (1 + exp(-z))
    ez = exp(z)
    return ez / (1 + ez)


def G(t, eta, rho):
    return 1 - step((t - eta) / (rho - eta))


def smooth_v(t, eta):
    # Equals 1 on [eta, 1/2], is supported in (eta/2, 3/5).
    return step((t - eta / 2) / (eta / 2)) * (1 - step((t - 0.5) / 0.1))


def middle_count(n, ds, eta):
    a, b = eta.numerator, eta.denominator
    lo, hi = n ** a, n ** (b - a)
    return sum(lo < d ** b < hi for d in ds)


def lambda_value(n, ds, mu, eta, rho):
    a, b = eta.numerator, eta.denominator
    c, dden = rho.numerator, rho.denominator
    value = 0.0
    for d in ds:
        if not mu[d]:
            continue
        # Enforce rational endpoint equalities exactly, not via floating log.
        if d ** b <= n ** a:
            gd = 1.0
        elif d ** dden >= n ** c:
            gd = 0.0
        else:
            gd = G(log(d) / log(n), float(eta), float(rho))
        value += mu[d] * gd
    return value


def check_pointwise(limit):
    spf, mu = arithmetic_tables(limit)
    etas = [Fraction(1, 12), Fraction(1, 6), Fraction(1, 4),
            Fraction(3, 10), Fraction(1, 3)]
    rho = Fraction(2, 5)
    checks = 0
    d0_composites = d1_composites = 0
    for n in range(2, limit + 1):
        fs = factor(n, spf)
        ds = divisors(fs)
        prime = len(fs) == 1 and fs[0][1] == 1
        square = isqrt(n) ** 2 == n
        prime_square = len(fs) == 1 and fs[0][1] == 2
        for eta in etas:
            a, b = eta.numerator, eta.denominator
            D = middle_count(n, ds, eta)
            lam = lambda_value(n, ds, mu, eta, rho)
            assert D % 2 == int(square), (n, eta, D)
            C = sum(d ** b > n ** a and d * d <= n for d in ds)
            assert 2 * C == D + int(square)
            if D == 0 and not prime:
                d0_composites += 1
                exceptional_cube = eta == Fraction(1, 3) and len(fs) == 1 and fs[0][1] == 3
                if not exceptional_cube:
                    P = fs[-1][0]
                    assert P ** b >= n ** (b - a), (n, eta, fs)
                    m = n // P
                    assert 1 < m and m ** b <= n ** a and gcd(P, m) == 1
                assert abs(lam) < 2e-12, (n, eta, lam)
            if D == 1:
                d1_composites += 1
                assert square and len(fs) == 1, (n, eta, fs)
                k = fs[0][1]
                assert k == 2 or (k == 4 and eta >= Fraction(1, 4)) or (k == 6 and eta == Fraction(1, 3))
                if k != 2:
                    assert abs(lam) < 2e-12
            if len(fs) == 1:
                k = fs[0][1]
                assert D == k - 2 * (k * a // b) - 1
                assert abs(lam - (1 - G(1 / k, float(eta), float(rho)))) < 2e-12
            sharp = lam * lam * (1 - D / 2) - int(prime_square) / 2
            unordered = lam * lam * (1 - C)
            smooth = lam * lam * (1 - sum(smooth_v(log(d) / log(n), float(eta)) for d in ds))
            assert sharp <= int(prime) + 2e-10, (n, eta, sharp)
            assert unordered <= int(prime) + 2e-10
            assert smooth <= unordered + 2e-10
            if prime:
                assert abs(sharp - 1) < 2e-12 and abs(smooth - 1) < 2e-12
            checks += 1

    # An exact frozen-window minorant, even at eta = 1/3.
    for X in (20, 100, 1000):
        Y = 2 * X
        if Y > limit:
            continue
        assert Y ** float(rho) <= sqrt(X) and sqrt(Y) < X
        for n in range(X, Y + 1):
            fs = factor(n, spf)
            ds = divisors(fs)
            prime = len(fs) == 1 and fs[0][1] == 1
            for eta in etas:
                a, b = eta.numerator, eta.denominator
                lam = sum(mu[d] * G(log(d) / log(Y), float(eta), float(rho)) for d in ds)
                C = sum(d ** b > X ** a and d * d <= Y for d in ds)
                assert lam * lam * (1 - C) <= int(prime) + 2e-10

    print(f'Pointwise tests: {checks} (n <= {limit}); D=0 composite cases: {d0_composites}; D=1 cases: {d1_composites}.')
    return spf, mu


def check_exact_expansion(spf, mu, limit=500):
    eta, rho = Fraction(1, 4), Fraction(2, 5)
    total = 0
    for n in range(2, min(limit, len(spf) - 1) + 1):
        ds = divisors(factor(n, spf))
        gd = {d: G(log(d) / log(n), float(eta), float(rho)) for d in ds}
        bcoeff = {}
        for d in ds:
            for e in ds:
                ell = lcm(d, e)
                bcoeff[ell] = bcoeff.get(ell, 0.0) + mu[d] * mu[e] * gd[d] * gd[e]
        lam = sum(mu[d] * gd[d] for d in ds)
        assert abs(sum(bcoeff.values()) - lam * lam) < 2e-10
        C = sum(k ** 4 > n and k * k <= n for k in ds)
        rhs = 0.0
        for ell, bell in bcoeff.items():
            if not bell:
                continue
            count = 0
            for r in divisors(factor(ell, spf)):
                for q in range(1, isqrt(n) // r + 1):
                    if gcd(q, ell // r) == 1 and n % (ell * q) == 0 and (r * q) ** 4 > n:
                        count += 1
            assert count == C
            rhs += bell * count
        assert abs(rhs - C * lam * lam) < 2e-9
        total += 1
    print(f'Exact lcm/gcd expansion: {total} integers checked.')


def check_density_kernel():
    s, t, u, x = sp.symbols('s t u x')
    q = s + t
    K = s * t * (s + u) * (t + u) / (u * q * (q + u))
    assert sp.factor(K - s * t / q - s ** 2 * t ** 2 / (q * u * (q + u))) == 0
    a, z = sp.symbols('eta z', real=True)
    at = z * (1 - z) - a * a
    h = 1 - 2 * z
    assert sp.expand(-sp.diff(at * sp.diff(h, z), z) - 2 * h) == 0
    Q1 = x * sp.atanh(x) - 1
    assert sp.simplify(-sp.diff((1 - x * x) * sp.diff(Q1, x), x) - 2 * Q1) == 0

    # Exact finite residue-space realization of 1/phi(lcm).
    coeff = {1: Fraction(1), 3: Fraction(-3, 5), 5: Fraction(-1, 3),
             7: Fraction(-1, 7), 15: Fraction(1, 10)}
    ks = (1, 3, 5, 7)
    M = lcm(*coeff.keys(), *ks)
    residues = [r for r in range(M) if gcd(r + 2, M) == 1]
    expectation = sum((sum(c for d, c in coeff.items() if r % d == 0)) ** 2 *
                      sum(r % k == 0 for k in ks) for r in residues) / len(residues)
    kernel_sum = sum(cd * ce / int(sp.totient(lcm(d, e, k)))
                     for k in ks for d, cd in coeff.items() for e, ce in coeff.items())
    assert expectation == kernel_sum and kernel_sum >= 0
    print('Symbolic polar/ground-state identities verified; finite positive-density kernel:', kernel_sum)


def check_variation():
    for eta, rho in ((0.05, 0.3), (0.1, 0.4), (0.1, 0.5), (1/3, 0.5)):
        c = sqrt(1 - 4 * eta * eta)
        h0, h1 = 1 - 2 * eta, 1 - 2 * rho
        Q = lambda h: (h / c) * atanh(h / c) - 1
        Acoef, Bcoef = np.linalg.solve([[h0, Q(h0)], [h1, Q(h1)]], [0.5, 0.5])
        def fbase(t):
            h = 1 - 2 * t
            return Acoef * h + Bcoef * Q(h) - 0.5
        def fpbase(t):
            x = (1 - 2 * t) / c
            return -2 * Acoef - 2 * Bcoef / c * (atanh(x) + x / (1 - x * x))
        S_integral = quad(fbase, eta, rho, epsabs=1e-12)[0]
        if rho == 0.5:
            S = (c * atanh(h0 / c) - h0) / 8
        else:
            B = (1 / h1 - 1 / h0) / 2
            R = (atanh(h0 / c) - atanh(h1 / c)) / (2 * c)
            S = (c * c * B * R / (B + R) - (rho - eta)) / 4
        assert abs(S - S_integral) < 2e-12
        M = quad(lambda t: (fbase(t) ** 2 - 0.5 * (t * (1 - t) - eta * eta) * fpbase(t) ** 2) / S ** 2,
                 eta, rho, epsabs=1e-8)[0]
        assert abs(M + 1 / (2 * S)) < 2e-7
        assert M < 0
        Rwidth = rho - eta
        assert M <= (2*Rwidth - 1)/(Rwidth*Rwidth) + 1e-7
        print(f'Sharp H^1 optimum eta={eta:.8g}, rho={rho:.8g}: {M:.12g}')

    # A genuinely C-infinity admissible f=-G', normalized to integral one.
    eta, rho = 0.1, 0.4
    width = rho - eta
    def bump(u):
        if not 0 < u < 1:
            return 0.0
        return exp(-1 / (u * (1 - u)))
    Z = quad(bump, 0, 1, epsabs=1e-13)[0]
    def f(t):
        return bump((t - eta) / width) / (width * Z)
    def fp(t):
        u = (t - eta) / width
        if not 0 < u < 1:
            return 0.0
        return bump(u) * (1 - 2*u) / (u*u*(1-u)*(1-u)) / (width*width*Z)
    I = quad(lambda t: f(t)**2, eta, rho)[0]
    cost = quad(lambda t: (t*(1-t)-eta*eta) * fp(t)**2, eta, rho)[0]
    gs = quad(lambda t: (t*(1-t)-eta*eta) * (fp(t) + 2*f(t)/(1-2*t))**2, eta, rho)[0]
    assert abs(cost - 2*I - gs) < 1e-7
    def density(u):
        return quad(lambda t: min(t, u)*fp(t)**2, eta, rho,
                    points=[u] if eta < u < rho else None)[0]
    penalty = quad(density, eta, 0.5, points=[rho], epsabs=1e-7)[0]
    assert abs(penalty - cost/2) < 1e-6
    print(f'C-infinity test: M={I-cost/2:.12g}; density integral and ground-state identity agree.')


def counterexamples():
    n = 101 * 103 * 107
    ds = sorted({101**i * 103**j * 107**k for i, j, k in product((0, 1), repeat=3)})
    assert middle_count(n, ds, Fraction(17, 50)) == 0
    assert all(log(p)/log(n) < 17/50 for p in (101, 103, 107))
    print(f'eta>1/3 failure: n={n}, eta=17/50, rho=2/5, D=0 and lambda=-2.')
    eta, rho = 0.25, 0.4
    g = G(log(3)/log(21), eta, rho)
    naive = g * (1-g)**2
    assert naive > 0
    print(f'Naively smoothed middle weight fails at n=21: positive composite value {naive:.12g}.')
    frozen_wrong = (1-G(log(3)/log(20), 1/3, 0.4))**2
    frozen_right = (1-G(log(3)/log(40), 1/3, 0.4))**2
    assert frozen_wrong > 0 and frozen_right == 0
    print(f'Lower-endpoint freezing fails at n=27, X=20: {frozen_wrong:.12g}; upper-endpoint freezing gives 0.')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--limit', type=int, default=20000)
    args = parser.parse_args()
    spf, mu = check_pointwise(args.limit)
    check_exact_expansion(spf, mu)
    check_density_kernel()
    check_variation()
    counterexamples()
    print('All checks passed.')


if __name__ == '__main__':
    main()
