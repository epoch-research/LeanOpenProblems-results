#!/usr/bin/env python3
"""Exact checks for the factorial-gap integral investigation.

These tests do not infer irrationality from finite computations.  The
infinite identities and inequalities are justified in the accompanying report;
the factorial-difference identity is also proved in Lean.
"""
from fractions import Fraction as Q
from math import comb, factorial, gcd, prod
from random import Random


def partial(n):
    return sum((Q(1, factorial(j) - 1) for j in range(2, n + 1)), Q())


def inside_gap_checks():
    count = 0
    for n in range(2, 19):
        f, a, d = factorial(n), factorial(n) - 1, n * factorial(n)
        assert gcd(a, d) == 1
        for m in range(0, n + 5):
            nodes = [a + j * d for j in range(m + 1)]
            den = prod(nodes)
            num = factorial(m) * d**m
            integral = sum((Q((-1)**j * comb(m, j), nodes[j])
                            for j in range(m + 1)), Q())
            assert integral == Q(num, den)
            g = gcd(den, factorial(m))
            assert integral.numerator == num // g
            assert integral.denominator == den // g
            assert integral.numerator >= d**m
            assert integral == Q(1, a) * prod(Q(j * d, a + j * d)
                                             for j in range(1, m + 1))
            if m <= n:
                assert g == 1
                assert all(gcd(nodes[i], nodes[j]) == 1
                           for i in range(m + 1) for j in range(i))
                assert all(factorial(n + 1) - 1 < nodes[j] < factorial(n + 2) - 1
                           for j in range(2, m + 1))
            count += 1
    return count


def ordinary_gap_checks():
    for n in range(2, 8):
        a, b = factorial(n) - 1, factorial(n + 1) - 1
        d = b - a
        D = a * comb(b, a)
        assert D == b * comb(b - 1, a - 1)
        assert gcd(a, b) == 1
        assert D % (a * b) == 0
        C = D // (a * b)
        # B(a,d+1)=1/D.  C is the least positive multiplier putting
        # the result in Z + Z/a + Z/b = (1/(a*b)) Z.
        assert Q(C, D) == Q(1, a * b)
        u = factorial(n - 1)
        v = (n + 1) * u + 1
        assert u * b - v * a == 1
        assert Q(u, a) - Q(v, b) == Q(1, a * b)
        # Direct factorial evaluation is inexpensive for the first cases.
        if n <= 5:
            assert Q(factorial(a - 1) * factorial(d), factorial(b)) == Q(1, D)
    assert (5 * comb(23, 5)) == 168245
    assert 168245 // (5 * 23) == 1463


def newton_value(coeffs, n):
    """p_math(n), with basis binom(n-1,j), for n>=1."""
    assert n >= 1
    return sum(c * comb(n - 1, j) for j, c in enumerate(coeffs) if j < n)


def residual(A, coeffs, k, n):
    f = factorial(n)
    h = n**k * newton_value(coeffs, n - 1) - newton_value(coeffs, n)
    value = Q(A, f - 1) + Q(h, f**k)
    numerator = A * f**k + (f - 1) * h
    assert numerator % (f - 1) == A % (f - 1)
    assert value == Q(numerator, (f - 1) * f**k)
    return value


def telescope_checks():
    rng = Random(68)
    for _ in range(80):
        coeffs = [rng.randrange(-20, 21) for _ in range(rng.randrange(1, 8))]
        A, k, N = rng.randrange(-20, 21), rng.randrange(1, 7), rng.randrange(2, 25)
        left = sum((residual(A, coeffs, k, n) for n in range(2, N + 1)), Q())
        right = A * partial(N) + coeffs[0] - Q(newton_value(coeffs, N), factorial(N)**k)
        assert left == right


# Exact polynomial arithmetic, coefficients in ascending degree order.
def padd(a, b):
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
            for i in range(max(len(a), len(b)))]


def pscale(a, c):
    return [c * x for x in a]


def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def pshift(a, s):
    out = [0] * len(a)
    for j, c in enumerate(a):
        for i in range(j + 1):
            out[i] += c * comb(j, i) * s**(j - i)
    return out


def peval(a, x):
    return sum(c * x**j for j, c in enumerate(a))


def example_check():
    cs = [-5, -3, -33, -299, 7995]
    # This is 24*p, so all following polynomial identities are integral.
    P = [198216, -411790, 286605, -81146, 7995]
    H = padd(pmul([0, 0, 0, 1], pshift(P, -1)), pscale(P, -1))
    shifted = pshift(H, 6)
    assert shifted == [33252216, 94909306, 99830511, 52658546,
                       15426137, 2549697, 222664, 7995]
    assert all(c > 0 for c in shifted)
    # Independently convert the Newton basis into the ordinary power basis.
    newton_poly = [Q()]
    term = [Q(1)]
    for j, c in enumerate(cs):
        if j:
            term = pscale(pmul(term, [-j, 1]), Q(1, j))
        newton_poly = padd(newton_poly, pscale(term, c))
    assert pscale(newton_poly, 24) == P
    assert peval(P, 1) == -120
    assert [peval(H, n) // 24 for n in range(2, 6)] == [-32, -172, -2404, -58084]
    assert residual(4, cs, 3, 2) == 0
    assert residual(4, cs, 3, 3) == Q(1, 270)
    assert all(residual(4, cs, 3, n) >= 0 for n in range(2, 6))
    # The positive coefficients of H(u+6) prove positivity for EVERY n>=6,
    # not merely for a tested finite range.
    # |R_n| <= C*n^7/n!; the report proves the geometric tail bound used here.
    C, M, degree = Q(8) + 2 * sum(abs(c) for c in newton_poly), 40, 7
    assert C == 82154
    assert M >= max(2, 2 * degree)
    upper = sum((residual(4, cs, 3, n) for n in range(2, M + 1)), Q())
    upper += C * Q(M + 2, M) * Q((M + 1)**degree, factorial(M + 1))
    assert Q(1, 270) < upper < Q(1, 71)
    return C, M


if __name__ == '__main__':
    cases = inside_gap_checks()
    ordinary_gap_checks()
    telescope_checks()
    C, M = example_check()
    print(f'PASS: {cases} exact inside-gap beta identities and primitive normalizations')
    print('PASS: ordinary-gap endpoint normalization and explicit Bezout identities')
    print('PASS: 80 exact finite factorial-difference identities and numerator congruences')
    print('PASS: exact polynomial positivity certificate for the primitive form 4*S-5')
    print(f'PASS: rigorous rational upper certificate uses C={C}, M={M}: 0 < 4*S-5 < 1/71')
    print('NO irrationality conclusion: no infinite shrinking certificate family is proved.')
