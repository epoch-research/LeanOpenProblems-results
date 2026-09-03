#!/usr/bin/env python3
"""Exact finite checks for SemiprimeDiagonalExtractionAudit.md.

Only integer/Fraction arithmetic is used.  Local Euler products are checked
as algebra, NOT asserted to be asymptotics for prime pairs.
"""
from fractions import Fraction as F
from itertools import product
from math import gcd, isqrt, prod


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def mark(r):
    # A nonnegative rational stand-in for a cofactor weight, on actual primes.
    return F(7 + r % 5, 7) if is_prime(r) else F(0)


def endpoints(X, h, clipped=True):
    if clipped:
        return range(max(X, X - h) + 1, min(2 * X, 2 * X - h) + 1)
    return range(X + 1, 2 * X + 1)


def component(p, n, weight=mark):
    return weight(n // p) if n % p == 0 else F(0)


def matrix(X, h, pool, clipped=True, mask=lambda n, h: F(1)):
    return {
        (p, q): sum((mask(n, h) * component(p, n)
                      * component(q, n + h)
                      for n in endpoints(X, h, clipped)), F(0))
        for p in pool for q in pool
    }


def corr_from_matrix(A, pool, w):
    return sum((w[p] * w[q] * A[p, q] for p in pool for q in pool), F(0))


def direct_corr(X, h, pool, w, clipped, mask):
    def lift(n):
        return sum((w[p] * component(p, n) for p in pool), F(0))
    return sum((mask(n, h) * lift(n) * lift(n + h)
                for n in endpoints(X, h, clipped)), F(0))


def crt_component(X, h, p, q, clipped, mask):
    assert p != q
    n0 = p * ((-h * pow(p, -1, q)) % q)
    a, b = n0 // p, (n0 + h) // q
    assert q * b - p * a == h
    lo = max(X, X - h) if clipped else X
    hi = min(2 * X, 2 * X - h) if clipped else 2 * X
    first = (lo - n0) // (p * q) + 1
    last = (hi - n0) // (p * q)
    return sum((mask(n0 + p * q * t, h) * mark(a + q * t) * mark(b + p * t)
                for t in range(first, last + 1)), F(0))


def check_extraction():
    pool = (3, 5, 7)
    c = {3: F(1), 5: F(2, 3), 7: F(-1, 2)}
    signs = tuple(product((-1, 1), repeat=len(pool)))
    masks = (lambda n, h: F(1),
             lambda n, h: F((n + 2 * h) % 5 != 0, 1 + n % 3))
    cases = crt_cases = 0
    for X, shifts in ((80, range(-17, 18)), (200, range(-40, 41)),
                      (300, (-36, 0, 36, 70))):
        for h in shifts:
            assert X - abs(h) > max(pool)**2
            for clipped in (False, True):
                for mask in masks:
                    A = matrix(X, h, pool, clipped, mask)
                    assert direct_corr(X, h, pool, c, clipped, mask) == corr_from_matrix(A, pool, c)
                    avg = sum((corr_from_matrix(A, pool,
                              {p: c[p] * s[i] for i, p in enumerate(pool)})
                               for s in signs), F(0)) / len(signs)
                    extracted = F(0)
                    for p in pool:
                        if h % p:
                            assert A[p, p] == 0
                            continue
                        k = h // p
                        lo = max(X, X - h) if clipped else X
                        hi = min(2 * X, 2 * X - h) if clipped else 2 * X
                        pair = sum((mask(p * r, h) * mark(r) * mark(r + k)
                                    for r in range(lo // p + 1, hi // p + 1)), F(0))
                        assert A[p, p] == pair
                        extracted += c[p]**2 * pair
                        # Both cross blocks vanish on a p-divisible shift.
                        for q in pool:
                            if q != p:
                                assert A[p, q] == A[q, p] == 0
                        plus = {q: F(1) for q in pool}
                        minus = plus.copy()
                        minus[p] = F(-1)
                        value = corr_from_matrix(A, pool, plus)
                        assert value == corr_from_matrix(A, pool, minus)
                        if h != 0 and h % 2 == 0:
                            # A formal rank-one comparison, not a pair asymptotic.
                            M = X * singular_truncated(h)
                            rest = sum((F(1, q) for q in pool if q != p), F(0))
                            err_plus = value - M * (rest + F(1, p))**2
                            err_minus = value - M * (rest - F(1, p))**2
                            assert max(abs(err_plus), abs(err_minus)) >= 2 * M * rest / p
                    assert avg == extracted
                    for p in pool:
                        for q in pool:
                            if p != q:
                                assert A[p, q] == crt_component(X, h, p, q, clipped, mask)
                                crt_cases += 1
                    cases += 1
    # Boundary deletion removes at most |h| terms for an unweighted lift.
    for h in range(-50, 51):
        def lift(n):
            return sum(n % p == 0 and is_prime(n // p) for p in pool)
        vals = [lift(n) * lift(n + h) for n in endpoints(300, h, False)]
        full = sum(vals)
        clipped = sum(lift(n) * lift(n + h) for n in endpoints(300, h, True))
        assert 0 <= full - clipped <= abs(h)
    return cases, crt_cases


def character_kernel_17(p, q):
    """Average conj(chi(p))*chi(q) in Q[zeta_16], Phi_16=z^8+1."""
    if p % 17 == 0 or q % 17 == 0:
        return [F(0)] * 8
    logs = {pow(3, j, 17): j for j in range(16)}
    d = (logs[q % 17] - logs[p % 17]) % 16
    answer = [F(0)] * 8
    for j in range(16):
        power = j * d % 16
        answer[power % 8] += F(1 if power < 8 else -1, 16)
    return answer


def check_characters():
    pool = (3, 5, 7, 11, 13, 17, 19)
    count = 0
    for p in pool:
        for q in pool:
            expected = int(gcd(p * q, 17) == 1 and (p - q) % 17 == 0)
            assert character_kernel_17(p, q) == [F(expected)] + [F(0)] * 7
            count += 1
    # Real characters mod 4 retain the collision 3 == 7 mod 4.
    for p in (3, 5, 7):
        for q in (3, 5, 7):
            chi_p, chi_q = (-1)**((p - 1) // 2), (-1)**((q - 1) // 2)
            assert F(1 + chi_p * chi_q, 2) == int((p - q) % 4 == 0)
    assert F(1 + (-1) * (-1), 2) == 1  # surviving off-diagonal (3,7)
    return count + 9


LOCAL_PRIMES = (2, 3, 5, 7, 11, 13, 17)


def singular_truncated(h):
    return prod((F(1) - F(1 if h % ell == 0 else 2, ell))
                / (1 - F(1, ell))**2 for ell in LOCAL_PRIMES)


def check_local_factors():
    count = 0
    for p in (3, 5, 7):
        for q in (3, 5, 7):
            for h in range(-60, 61):
                if h == 0:
                    continue
                if p == q:
                    if h % p == 0:
                        ratio = F(1) if (h // p) % p == 0 else F(p - 2, p - 1)
                        assert singular_truncated(h // p) == singular_truncated(h) * ratio
                    continue
                n0 = p * ((-h * pow(p, -1, q)) % q)
                a, b = n0 // p, (n0 + h) // q
                local = F(1)
                for ell in LOCAL_PRIMES:
                    nu = sum((a + q * t) * (b + p * t) % ell == 0 for t in range(ell))
                    if ell == p:
                        expected_nu = ell if h % p == 0 else 1
                    elif ell == q:
                        expected_nu = ell if h % q == 0 else 1
                    else:
                        expected_nu = 1 if h % ell == 0 else 2
                    assert nu == expected_nu
                    local *= (1 - F(nu, ell)) / (1 - F(1, ell))**2
                expected = (F(0) if h % p == 0 or h % q == 0 else
                            singular_truncated(h) * F(p - 1, p - 2) * F(q - 1, q - 2))
                assert local == expected
                count += 1
    return count


def check_support_and_bins():
    count = 0
    pool = (11, 13, 17, 19)
    for p in pool:
        for k in range(1, min(pool)):
            h = p * k
            assert [q for q in pool if h % q == 0] == [p]
            assert h % (p * p) != 0
            count += 1
    # m comparable factors have averaged trace/coherent mass of order 1/m.
    for r, pool in ((10, (11, 13, 17, 19)), (20, (23, 29, 31, 37))):
        for chosen in product((0, 1), repeat=len(pool)):
            J = [p for p, take in zip(pool, chosen) if take]
            if not J:
                continue
            lam = sum((F(1, p) for p in J), F(0))
            mu = sum((F(1, p * p) for p in J), F(0))
            assert F(1, len(J)) <= mu / lam**2 <= F(4, len(J))
            assert F(len(J), 2 * r) <= lam <= F(len(J), r)
            count += 1
    return count


def check_variance():
    # Exact periodic version of the positivity inequality used for B_1.
    N, X, pool = 64, 300, (3, 5, 7)
    seqs = [[component(p, X + j) for j in range(N)] for p in pool]
    count = 0
    for y in (1, 2, 4, 8, 16):
        def variance(seq):
            mean = sum(seq, F(0)) / N
            averages = [sum((seq[(j + t) % N] for t in range(1, y + 1)), F(0)) / y
                        for j in range(N)]
            return sum(((a - mean)**2 for a in averages), F(0))
        individual = sum((variance(seq) for seq in seqs), F(0))
        avg = F(0)
        for s in product((-1, 1), repeat=len(pool)):
            combined = [sum((s[i] * seqs[i][j] for i in range(len(pool))), F(0))
                        for j in range(N)]
            avg += variance(combined) / 2**len(pool)
        assert avg == individual
        lower = sum((sum((u * u for u in seq), F(0)) / y
                     - sum(seq, F(0))**2 / N for seq in seqs), F(0))
        assert individual >= lower
        count += 1
    return count


def check_exponents():
    alpha1, alpha2 = F(3, 34), F(2, 17)
    assert 1 / (2 * (alpha2 - alpha1)) == 17
    assert 2 * alpha1 * 17 == 3
    assert F(19, 17) < 2
    # A positive small-slack example, not an assertion of optimal eta.
    e, ep, delta = F(1, 1000), F(1, 10**8), F(1, 10**9)
    a, b = 1 + e * e, 17 + e
    small_G = 2 * (alpha1 - ep) * b - (3 + 2 * e * e) * a - b * delta
    remainder = a * e * e
    minor_Q0 = a - 1 - b * delta
    assert 0 < min(small_G, remainder, minor_Q0)
    assert max(small_G, remainder, minor_Q0) < F(1, 100)
    assert 1 - b * delta > F(99, 100)


def check_consecutivity():
    p, r, k, X = 3, 101, 12, 300
    assert X < p * r < p * (r + k) <= 2 * X
    assert is_prime(r) and is_prime(r + k)
    intervening = [r + j for j in range(1, k) if is_prime(r + j)]
    assert intervening == [103, 107, 109]
    return intervening


if __name__ == '__main__':
    e, c = check_extraction()
    chars = check_characters()
    local = check_local_factors()
    supports = check_support_and_bins()
    variances = check_variance()
    check_exponents()
    intervening = check_consecutivity()
    print(f'PASS: {e} extraction/mask/boundary cases; {c} CRT off-diagonal checks;')
    print(f'      {chars} character kernels; {local} local Euler-factor checks;')
    print(f'      {supports} support/bin checks; {variances} exact variance checks.')
    print('      Rank-one rigidity and exact exponent-budget checks PASS.')
    print(f'Consecutivity counterexample: 101,113 have interior primes {intervening}.')
    print('No prime-pair asymptotic, limit statement, or Lean axiom is tested or assumed.')
