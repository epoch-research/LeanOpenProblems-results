#!/usr/bin/env python3
"""Finite checks for MixedHigherMomentAttempt.md; not a prime-gap proof."""
from decimal import Decimal, getcontext
from fractions import Fraction as Q
from hashlib import sha256
from itertools import product
from math import comb, exp, log
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SPEC_HASH = "47104279c0cb871e0a255d81fffde6a4a6ea7e71c3eec5c5b57e0bc7c0654123"


def check_cubic():
    for L in list(range(2, 40)) + [100, 1200]:
        mu = Q(1, comb(L, 2))
        h = Q(2 * (L + 1), 3)
        vals = [Q(v) - mu * comb(v, 3) for v in range(2 * L + 3)]
        assert max(vals) == h
        assert [v for v, val in enumerate(vals) if val == h] == [L, L + 1]
        for v in range(2 * L + 2):
            assert vals[v + 1] - vals[v] == 1 - mu * comb(v, 2)
        # Under the ideal J_r/I=((L+1)/K)^r ratios, derive the finite cutoff.
        for K in [2 * (L + 1), 4 * (L + 1), 100 * (L + 1)]:
            triple_integral_sum = 2 * comb(K // 2, 3) * Q(L + 1, K) ** 3
            derived = (Q(L + 1) - h) / (mu * triple_integral_sum)
            displayed = Q(4 * L * (L - 1), (L + 1) ** 2) / (
                (1 - Q(2, K)) * (1 - Q(4, K))
            )
            assert derived == displayed
            assert derived == 4 if K == 2 * (L + 1) else derived < 4
    print("PASS: cubic maxima, differences, and finite threshold (exact rationals)")


def check_chen_polynomial():
    # Exact majorant in terms of the number of distinct interval primes.
    for rough in [0, 1]:
        for k in range(30):
            R, D, T = Q(rough), Q(rough * k), Q(rough * max(k - 2, 0))
            U = R - D / 2 + T / 2
            expected = Q(0) if not rough or k >= 2 else Q(1) if k == 0 else Q(1, 2)
            assert U == expected and 0 <= U <= 1
    # Polynomial coefficients: rows/columns are R,D,T, without identifying
    # the two coordinates or multiplying marginal estimates.
    v = [Q(1), Q(-1, 2), Q(1, 2)]
    expected_coefficients = [
        [Q(1), Q(-1, 2), Q(1, 2)],
        [Q(-1, 2), Q(1, 4), Q(-1, 4)],
        [Q(1, 2), Q(-1, 4), Q(1, 4)],
    ]
    assert [[a * b for b in v] for a in v] == expected_coefficients
    for kj, kk in product(range(12), repeat=2):
        aj = [Q(1), Q(kj), Q(max(kj - 2, 0))]
        ak = [Q(1), Q(kk), Q(max(kk - 2, 0))]
        direct = sum(a * b for a, b in zip(v, aj)) * sum(a * b for a, b in zip(v, ak))
        expanded = sum(expected_coefficients[a][b] * aj[a] * ak[b]
                       for a in range(3) for b in range(3))
        assert direct == expanded
    print("PASS: exact Chen majorant and all nine mixed coefficients")


def check_one_island_model():
    # Select one group uniformly, then independent Bernoulli(2p) at each
    # of its q sites. These are scalar countermodels, not integer primes.
    for q in range(3, 10):
        for p in [Q(1, 20), Q(1, 5), Q(1, 2)]:
            mass = {(x, 0): Q(1, 2) * comb(q, x) * (2 * p) ** x * (1 - 2 * p) ** (q - x)
                    for x in range(q + 1)}
            for y in range(q + 1):
                mass[(0, y)] = mass.get((0, y), Q(0)) + (
                    Q(1, 2) * comb(q, y) * (2 * p) ** y * (1 - 2 * p) ** (q - y)
                )
            assert sum(mass.values()) == 1
            assert all(x * y == 0 for x, y in mass)
            for r in range(1, min(5, q) + 1):
                lhs = sum(w * comb(x, r) for (x, _), w in mass.items())
                assert lhs == 2 ** (r - 1) * comb(q, r) * p ** r
            for L in range(2, q):
                mu, h = Q(1, comb(L, 2)), Q(2 * (L + 1), 3)
                meanQ = sum(w * (x + y - h - mu * (comb(x, 3) + comb(y, 3)))
                            for (x, y), w in mass.items())
                assert meanQ <= 0
    print("PASS: finite active-one-island model has r-point factors 2^(r-1)")


def simpson(f, a, b, n=20000):
    assert n % 2 == 0
    step = (b - a) / n
    return step / 3 * (f(a) + f(b) +
                       4 * sum(f(a + step * j) for j in range(1, n, 2)) +
                       2 * sum(f(a + step * j) for j in range(2, n, 2)))


def check_integrals():
    # Product-test moments, using z=log(1+a*u) as an independent quadrature.
    for a in [2.0, 5.0, 10.0]:
        c2 = (1 - exp(-a)) / a
        mean = (a - 1 + exp(-a)) / (a * (1 - exp(-a)))
        second = (exp(a) - 2 * a - exp(-a)) / (a * a * (1 - exp(-a)))
        c2_quad = simpson(lambda z: exp(-z) / a, 0.0, a)
        mean_quad = simpson(lambda z: (1 - exp(-z)) / (a * a), 0.0, a) / c2
        second_quad = simpson(lambda z: (exp(z) - 2 + exp(-z)) / (a ** 3), 0.0, a) / c2
        assert abs(c2 - c2_quad) < 1e-11
        assert abs(mean - mean_quad) < 1e-11
        assert abs(second - second_quad) < 1e-10 * max(1, second)
    for K in [10 ** 4, 10 ** 6, 10 ** 8]:
        a = log(K) - 2 * log(log(K))
        T = (exp(a) - 1) / a
        mean = (a - 1 + exp(-a)) / (a * (1 - exp(-a)))
        second = (exp(a) - 2 * a - exp(-a)) / (a * a * (1 - exp(-a)))
        for r in range(4):
            margin = K - r * T - (K - r) * mean
            assert margin > 0
            chebyshev = (K - r) * (second - mean * mean) / margin ** 2
            assert 0 < chebyshev < 2 / log(K) ** 2
    print("PASS: product-test moment integrals and sample Chebyshev margins")
    # On the triangle of side sigma: constant G_uv=2/sigma^2.
    for sigma in [Q(1, 4), Q(1, 5), Q(1, 7)]:
        area = sigma ** 2 / 2
        derivative = 2 / sigma ** 2
        assert area * derivative == 1
        assert area * derivative ** 2 == 2 / sigma ** 2
    assert 2 / Q(1, 4) ** 2 == 32
    assert (1 / Q(1, 8)) ** 2 == 64
    # Vector lower-sieve feasibility at the published alpha,beta.
    alpha, beta = Q(1, 7), Q(3, 14)
    assert (Q(1, 2) - alpha) / alpha == Q(5, 2)
    assert (Q(1, 2) - beta) / alpha == 2
    assert Q(5, 2) < 4  # no feasible pair with s_1,s_2 >= 2
    getcontext().prec = 60
    s = Decimal(7) / Decimal(4)
    H = 2 * s * s - s * s * s.ln() - 2 * s + Decimal(1) / 2
    cost = Decimal(49) / H
    sq = 1.75
    H_quad = sq * sq / 2 - 2 * simpson(lambda u: (sq - u) * log(u), 1.0, sq)
    assert abs(float(H) - H_quad) < 1e-11
    assert Decimal(34) < cost < Decimal(35)
    omega1 = 4 + 4 * simpson(lambda z: log(z - 2) / (z - 1), 3.0, 3.5)
    omega2 = 7 * simpson(lambda t: log(2.5 - 7 * t) / (3.5 - 7 * t) / t,
                         1 / 7, 3 / 14)
    assert abs(omega1 - 4.186441174825623) < 1e-11
    assert abs(omega2 - 0.2796617622384349) < 1e-11
    # Use the SOURCE'S Omega3 bound, not a newly certified quadrature.
    assert Q(419, 100) - Q(279, 1000) + Q(76, 1000) == Q(3987, 1000)
    print("PASS: simplex normalization and vector level constraint")
    print("H(7/4) =", H)
    print("HBL kernel multiplier =", cost)
    print("Omega1 numerical check =", omega1)
    print("Omega2 numerical check =", omega2)


def check_files():
    digest = sha256((ROOT / "Spec.lean").read_bytes()).hexdigest()
    assert digest == SPEC_HASH
    report = (ROOT / "MixedHigherMomentAttempt.md").read_bytes()
    assert b"\x00" not in report
    assert b"(MC3)" in report
    print("PASS: Spec.lean unchanged; report contains no NUL byte")


if __name__ == "__main__":
    check_cubic()
    check_chen_polynomial()
    check_one_island_model()
    check_integrals()
    check_files()
    print("These checks do not prove MC3 or Erdős #5.")
