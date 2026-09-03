#!/usr/bin/env python3
"""Finite audits for FourierComparabilityResearch.md.

These checks do NOT prove an asymptotic estimate or a dispersion theorem.
All arithmetic identities are tested with integers; Fourier checks use mpmath.
No Lean declaration, in particular Spec.lean, is imported or used.
"""
from array import array
from fractions import Fraction
from math import gcd, isqrt, log, exp
from pathlib import Path
import cmath
import hashlib
import mpmath as mp

ROOT = Path(__file__).resolve().parent
SPEC_SHA = "d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb"
assert hashlib.sha256((ROOT / "Spec.lean").read_bytes()).hexdigest() == SPEC_SHA

MAX = 1_000_001
P = array('I', [0]) * (MAX + 1)
P[1] = 1
primes = []
for p in range(2, MAX + 1):
    if P[p] == 0:
        primes.append(p)
        for m in range(p, MAX + 1, p):
            P[m] = p


def factors(n):
    out = []
    while n > 1:
        p = P[n]
        a = 0
        while n % p == 0:
            n //= p
            a += 1
        out.append((p, a))
    return out


def sig(a):
    return (a > 0) - (a < 0)


# Exact constants in the analytic range.
beta = Fraction(51, 100)
assert Fraction(1, 2) < beta < Fraction(17, 33)
assert Fraction(17, 36) - Fraction(11, 12) * beta == Fraction(17, 3600)
assert 2 * beta - 1 == Fraction(1, 50)
print("Exact margins: FR=17/3600, high-cofactor=1/50")

# Radical square-divisor and cofactor identities, including prime powers.
rad_checks = 0
cofactor_checks = 0
for n in range(2, 100_001):
    rad = 1
    d = 1
    tau3 = 1
    fac = factors(n)
    for p, a in fac:
        rad *= p
        d *= p ** (a // 2)
        tau3 *= (a + 1) * (a + 2) // 2
    assert n % (d * d) == 0
    assert d * d >= n // rad
    assert 3 ** len(fac) <= tau3
    m = n // P[n]
    rad_m = 1
    for p, a in factors(m):
        rad_m *= p
    assert m // rad_m <= n // rad
    rad_checks += 1

    p, q = P[n], P[n + 1]
    assert p != q
    a, b = n // p, (n + 1) // q
    assert gcd(a, b) == 1
    assert b * q - a * p == 1
    c = p % b
    dd = (a * c + 1) // b
    assert b * dd - a * c == 1
    t = (p - c) // b
    assert p == b * t + c and q == a * t + dd
    assert t <= n // (a * b)
    cofactor_checks += 1
print(f"Exact radical/divisor bounds: {rad_checks}; cofactor parametrizations: {cofactor_checks}")

# Local sieve root counts, with inadmissibility at 2 retained.
root_checks = 0
small_primes = [p for p in primes if p <= 43]
for a in range(1, 51):
    for b in range(1, 51):
        if gcd(a, b) != 1:
            continue
        c = 0 if b == 1 else (-pow(a, -1, b)) % b
        d = (a * c + 1) // b
        assert b * d - a * c == 1
        assert gcd(b, c) == gcd(a, d) == 1
        for ell in small_primes:
            roots = sum(((b * t + c) * (a * t + d)) % ell == 0
                        for t in range(ell))
            assert roots == (1 if a * b % ell == 0 else 2)
            root_checks += 1
print(f"Exact two-linear-form local root counts: {root_checks}")

# Unique first-occupied-cell extraction and arbitrary high-P test identity.
U, V = 5, 97
cells = [(5, 11), (11, 23), (23, 47), (47, 97)]
limit = 30_000
encoded = array('I', [0]) * (limit + 1)
for lo, hi in cells:
    cell_primes = [p for p in primes if lo < p <= hi]
    for r in cell_primes:
        for m in range(1, limit // r + 1):
            if all(not (U < p <= hi) for p, _ in factors(m)):
                encoded[r * m] += 1

extract_checks = 0
for n in range(1, limit + 1):
    fac = factors(n)
    occupied = []
    for lo, hi in cells:
        entries = [(p, a) for p, a in fac if lo < p <= hi]
        if entries:
            occupied = (lo, hi, entries)
            break
    good = bool(occupied) and sum(a for p, a in occupied[2]) == 1
    assert encoded[n] == int(good)
    if good:
        lo, hi, entries = occupied
        r = entries[0][0]
        m = n // r
        assert all(not (U < p <= hi) for p, a in factors(m))
        assert (P[n] if P[n] > V else 0) == (P[m] if P[m] > V else 0)
        extract_checks += 1
print(f"Exact first-cell convolution checks: {limit}; good extractions: {extract_checks}")

# Formula (26), with the exact endpoint correction, at rational cutoffs.
endpoint_checks = 0
nonzero_endpoints = []
Xs = list(range(3, 301)) + [503, 1003, 1719, 3000, 5000, 10000, 30000]
for X in Xs:
    for b in [Fraction(51, 100), Fraction(3, 5), Fraction(2, 3)]:
        I = [p for p in primes if p * p > X and p ** b.denominator <= X ** b.numerator]
        Iset = set(I)
        lhs = sum(sig(P[n + 1] - P[n])
                  for n in range(1, X) if min(P[n], P[n + 1]) in Iset)
        plus = sum(P[m] > p for p in I for m in range(1, X + 1) if m % p == 1)
        minus = sum(P[m] > p for p in I for m in range(1, X + 1) if m % p == p - 1)
        endpoint = sum((X + 1) % p == 0 and P[X] > p for p in I)
        assert lhs == plus - minus + endpoint
        assert endpoint <= 2
        if endpoint and b == Fraction(51, 100):
            nonzero_endpoints.append((X, I, endpoint, lhs, plus - minus))
        endpoint_checks += 1
assert any(x[0] == 1719 for x in nonzero_endpoints)
print(f"Exact signed-sector endpoint checks: {endpoint_checks}")
print("Nonzero endpoint example:", next(x for x in nonzero_endpoints if x[0] == 1719))

# CRT root and prefix counts, both signs, without a hidden rounding loss.
crt_checks = 0
for p in [p for p in primes if p <= 41]:
    for q in [q for q in primes if q <= 41]:
        if p == q:
            continue
        for r in [-1, 1]:
            root = (p * ((r * pow(p, -1, q)) % q)) % (p * q)
            assert root % p == 0 and root % q == r % q
            for X in [p * q, p * q + 3, 2 * p * q + 7]:
                count = sum(n % p == 0 and (n - r) % q == 0 for n in range(1, X + 1))
                assert abs(count - X / (p * q)) <= 1
                assert count * p * q <= 2 * X
                crt_checks += 1
print(f"Exact CRT prefix checks: {crt_checks}")

# Finite positive tensor averaging: tests the exact triangle-inequality step,
# not the asserted analytic size of the discrepancies.
tensor_checks = 0
for X in [200, 503, 1719]:
    I = [p for p in primes if p * p > X and p ** 5 <= X ** 3]
    L = log(X)
    for r in [-1, 1]:
        total_error = 0j
        rhs = 0.0
        frequencies = [0., .3, 1., 3.1, 10., 37., 12345.6]
        weights = [2. / len(frequencies)] * len(frequencies)
        for freq, weight in zip(frequencies, weights):
            one_error = 0j
            error_sum = 0.
            for p in I:
                values = [0j] + [cmath.exp(2j * mp.pi * freq * log(P[m]) / L)
                                  if P[m] * P[m] > X else 0j for m in range(1, X + 1)]
                progression = sum(values[m] for m in range(1, X + 1) if m % p == r % p)
                principal = sum(values[m] for m in range(1, X + 1) if m % p != 0) / (p - 1)
                discrepancy = progression - principal
                one_error += cmath.exp(-2j * mp.pi * freq * log(p) / L) * discrepancy
                error_sum += abs(discrepancy)
            assert abs(one_error) <= error_sum + 1e-8
            total_error += weight * one_error
            rhs += weight * error_sum
            tensor_checks += 1
        assert abs(total_error) <= rhs + 1e-8
print(f"Finite positive-Fourier tensor checks: {tensor_checks}")

# Fourier transform of the tent, including its normalization.
mp.mp.dps = 45
fourier_checks = 0
for delta in [mp.mpf('0.001'), mp.mpf('0.03'), mp.mpf('0.5')]:
    def phi(v):
        return max(mp.mpf(0), 2 * (1 - abs(v) / (2 * delta)))
    for scaled in [mp.mpf(0), mp.mpf('0.1'), mp.mpf('0.7'), mp.mpf('2.2')]:
        t = scaled / delta
        transform = mp.quad(lambda v: phi(v) * mp.cos(2 * mp.pi * t * v),
                            [-2 * delta, 0, 2 * delta])
        expected = (4 * delta if not t else
                    4 * delta * (mp.sin(2 * mp.pi * delta * t) / (2 * mp.pi * delta * t)) ** 2)
        assert abs(transform - expected) < mp.mpf('1e-38')
        fourier_checks += 1
    for j in range(-200, 201):
        v = delta * j / 100
        if abs(v) <= delta:
            assert phi(v) >= 1 - mp.mpf('1e-40')
        assert phi(v) >= 0

# Integral of sinc^2: the omitted tail has the explicit bound 1/R.
R = 80 * mp.pi
sinc_int = mp.quad(lambda u: (mp.sin(u) / u) ** 2 if u else mp.mpf(1),
                  [j * mp.pi for j in range(81)])
mass_lower = 4 / mp.pi * sinc_int
mass_upper = mass_lower + 4 / (mp.pi * R)
assert mass_lower < 2 < mass_upper
print(f"Numerical Fourier transform checks: {fourier_checks}")
print("Fourier mass interval (explicit tail bound):", mp.nstr(mass_lower, 15), mp.nstr(mass_upper, 15))

arctan_checks = 0
for v_over_tau in [-5, -1, mp.mpf('-.1'), mp.mpf('.1'), 1, 5]:
    value = mp.quad(lambda s: mp.exp(-s) * mp.sin(v_over_tau * s) / s if s else v_over_tau,
                    [0, 1, 2, 4, 8, 16, 32, 64, 128])
    assert abs(value - mp.atan(v_over_tau)) < mp.mpf('1e-35')
    for tau in [mp.mpf('.001'), mp.mpf('.02')]:
        v = v_over_tau * tau
        H = mp.mpf('.5') + mp.atan(v / tau) / mp.pi
        error = abs((1 if v > 0 else 0) - H)
        assert error <= min(1, tau / abs(v))
    arctan_checks += 1
print(f"Numerical arctangent checks: {arctan_checks}")

# Finite data only: no limiting conclusion is inferred.
print("Finite data (prefix n<X; ratios compared exactly):")
for X in [1000, 10000, 100000, 1000000]:
    asc = sum(P[n + 1] > P[n] for n in range(1, X))
    close_3_2 = sum(2 * max(P[n], P[n + 1]) <= 3 * min(P[n], P[n + 1])
                    for n in range(1, X))
    close_2 = sum(max(P[n], P[n + 1]) <= 2 * min(P[n], P[n + 1])
                  for n in range(1, X))
    Iset = {p for p in primes if p * p > X and p ** 100 <= X ** 51}
    current = sum(sig(P[n + 1] - P[n]) for n in range(1, X)
                  if min(P[n], P[n + 1]) in Iset)
    print(f"  X={X}: ascents={asc}, close(R=3/2)={close_3_2}, close(R=2)={close_2}, central signed current={current}")

assert hashlib.sha256((ROOT / 'Spec.lean').read_bytes()).hexdigest() == SPEC_SHA
print('Spec.lean SHA-256 unchanged:', SPEC_SHA)
print('ALL FINITE CHECKS PASSED. Analytic/asymptotic claims require the written proof and cited theorems.')
