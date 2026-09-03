#!/usr/bin/env python3
"""Finite exact checks for FurstenbergObstructionResearch.md.

No Lean files are read as theorems or edited.  No asymptotic cancellation is
inferred from these checks.  The infinite statements have proofs in the note.
"""
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import gcd, isqrt, lcm, prod
from pathlib import Path
import hashlib

SPEC_HASH = "d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb"


def primes_upto(n):
    a = [True] * (n + 1)
    if n >= 0:
        a[0] = False
    if n >= 1:
        a[1] = False
    for p in range(2, isqrt(n) + 1):
        if a[p]:
            for t in range(p * p, n + 1, p):
                a[t] = False
    return [p for p in range(2, n + 1) if a[p]]


def valuation(n, p):
    assert n != 0
    n = abs(n)
    v = 0
    while n % p == 0:
        v += 1
        n //= p
    return v


def phi(n):
    result, rem = n, n
    for p in primes_upto(isqrt(n) + 1):
        if rem % p == 0:
            result -= result // p
            while rem % p == 0:
                rem //= p
    if rem > 1:
        result -= result // rem
    return result


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


@lru_cache(None)
def cyclotomic_value(d, a):
    proper = prod(cyclotomic_value(e, a) for e in divisors(d) if e < d)
    q, r = divmod(a**d - 1, proper)
    assert r == 0 and q >= 1
    return q


def crt(residues, moduli):
    M = prod(moduli)
    assert all(gcd(a, b) == 1 for i, a in enumerate(moduli) for b in moduli[i + 1:])
    return sum(r * (M // m) * pow(M // m, -1, m)
               for r, m in zip(residues, moduli)) % M


def exponent_data(H, moduli):
    assert len(moduli) == H
    base_primes = primes_upto(max(H, 2))
    M = prod(moduli)
    exponents = {
        p: crt([valuation(j, p) for j in range(1, H + 1)], moduli)
        for p in base_primes
    }
    for p, e in exponents.items():
        assert 0 <= e < M
        for j, m in enumerate(moduli, 1):
            assert (e - valuation(j, p)) % m == 0
    return M, exponents


def test_crt_and_cyclotomic():
    checks = 0
    for H in range(1, 9):
        mods = primes_upto(40)[1:H + 1]
        M, exps = exponent_data(H, mods)
        for t in (1, 2, 7):
            for j, m in enumerate(mods, 1):
                for p, e in exps.items():
                    exponent = e + M * t
                    a_exp, rem = divmod(exponent - valuation(j, p), m)
                    assert rem == 0 and a_exp >= 0
                    assert valuation(j, p) + m * a_exp == exponent
                    checks += 1

    # Pairwise coprime odd squarefree choices with a common small totient ratio.
    mods = [3, 5 * 7, 11 * 13 * 17]
    assert all(Fraction(phi(m), m) < Fraction(4, 5) for m in mods)
    exponent_data(3, mods)

    for a in range(2, 26):
        for m in range(3, 34, 2):
            minus = [cyclotomic_value(d, a) for d in divisors(m)]
            plus = [cyclotomic_value(2 * d, a) for d in divisors(m)]
            assert prod(minus) == a**m - 1
            assert prod(plus) == a**m + 1
            for d in divisors(m):
                assert phi(2 * d) == phi(d) <= phi(m)
                assert cyclotomic_value(d, a) <= (a + 1)**phi(d)
                assert cyclotomic_value(2 * d, a) <= (a + 1)**phi(d)
                checks += 2

    M, exps = exponent_data(3, [3, 5, 7])
    assert M == 105 and exps == {2: 21, 3: 15}
    N = 2**21 * 3**15
    bases = [31104, 432, 72]
    certificates = []
    for j, (a, m) in enumerate(zip(bases, [3, 5, 7]), 1):
        assert N == j * a**m
        for sign in (-1, 1):
            values = [cyclotomic_value(d if sign == -1 else 2 * d, a)
                      for d in divisors(m)]
            assert j * prod(values) == N + sign * j
            # All prime factors lie in one integer factor or in j.
            max_factor = max([j] + values)
            assert max_factor**10 < (N + sign * j)**9
            certificates.append((sign * j, max_factor))
            checks += 1
    assert 3**10 < N**9
    print(f"CRT/cyclotomic exact checks: {checks}")
    print(f"Explicit smooth block center N={N}")
    print("Maximal integer-factor certificates for offsets:", sorted(certificates))


def test_factorial_block():
    checks = 0
    for H in range(3, 36):
        B = lcm(*range(1, H + 1))
        L = B * B
        assert L > 2 * H
        ps = primes_upto(H)
        for r in range(1, H + 1):
            assert L % r == 0
            for sign in (-1, 1):
                C = L // r + sign
                assert C > 1 and gcd(C, B) == 1
                assert L + sign * r == r * C
                for p in ps:
                    assert valuation(L, p) > valuation(r, p)
                    assert valuation(L + sign * r, p) == valuation(r, p)
                    assert C % p != 0
                    checks += 1
    print(f"Factorial valuation and rough-cofactor checks: {checks}")


def test_projective():
    checks = 0
    integral_cases = 0
    for K in range(1, 5):
        for a, b, c, d in product(range(-K, K + 1), repeat=4):
            determinant = a * d - b * c
            if determinant == 0:
                continue
            assert abs(determinant) <= 2 * K * K
            threshold = 2 * K * K + K
            for n in (threshold + 1, threshold + 2, 10 * threshold + 1):
                numerator, denominator = a * n + b, c * n + d
                assert denominator != 0
                common = gcd(numerator, denominator)
                assert determinant % common == 0
                reduced = abs(denominator) // common
                if c:
                    assert reduced * (2 * K * K) >= n - K
                    assert reduced > 1
                if numerator % denominator == 0 and numerator // denominator > 0:
                    assert c == 0 and a * d > 0
                    integral_cases += 1
                checks += 1
    print(f"Projective exact cases: {checks}; positive integral cases: {integral_cases}")


def test_affine_finite_model():
    # Z_n = U+nV over F_q.  Every distinct-time pair is independent if q
    # does not divide the difference.  This is the exact finite analogue
    # of the onto torus homomorphism argument, not a simulation of it.
    pair_checks = 0
    for q in (7, 11, 17):
        times = range(-(q // 2), q // 2 + 1)
        for r in times:
            for s in times:
                if r == s:
                    continue
                counts = [[0] * q for _ in range(q)]
                for u, v in product(range(q), repeat=2):
                    counts[(u + r * v) % q][(u + s * v) % q] += 1
                assert all(x == 1 for row in counts for x in row)
                pair_checks += 1

        # Dilation preserving the complete finite process whenever k is a unit.
        for k in range(1, q):
            assert len({(u, k * v % q) for u, v in product(range(q), repeat=2)}) == q * q

        for v in range(1, q):
            ascents = sum((u + v) % q > u for u in range(q))
            descents = sum((u + v) % q < u for u in range(q))
            assert ascents == q - v and descents == v
            assert Fraction(ascents - descents, q) == 1 - Fraction(2 * v, q)
            assert (-v) % q == q - v

        # Gram certificate: complex characters have frequency vectors
        # (j, n*j). Distinct such vectors are exactly orthogonal under
        # uniform (U,V), by the finite geometric-series identity.
        vectors = [(j % q, n * j % q) for j in range(1, 4) for n in range(-2, 3)]
        assert len(vectors) == len(set(vectors))

        # Exact mean-square short-interval identity for a centered test.
        values = [Fraction(2 * z - (q - 1), 2) for z in range(q)]
        variance = sum(x * x for x in values) / q
        for length in (1, 2, q // 2, q):
            mean_square = sum(
                (sum(values[(u + n * v) % q] for n in range(1, length + 1)) / length)**2
                for u, v in product(range(q), repeat=2)
            ) / (q * q)
            assert mean_square == variance / length

    print(f"Affine finite-field pair-law checks: {pair_checks}; exact current/Gram/mean-square checks passed")


def test_rank_projection():
    # Noncoordinate rational subspaces: exact Gram--Schmidt, with no
    # square roots. This checks the finite trace identity used in (17).
    from random import Random
    random = Random(371)

    def dot(a, b):
        return sum(x * y for x, y in zip(a, b))

    checks = 0
    for R in range(1, 8):
        dimension = R + 1
        for _ in range(12):
            columns = [[Fraction(random.randrange(-3, 4)) for _ in range(dimension)]
                       for _ in range(R)]
            orthogonal = []
            for column in columns:
                residual = column[:]
                for w in orthogonal:
                    coefficient = dot(residual, w) / dot(w, w)
                    residual = [a - coefficient * b for a, b in zip(residual, w)]
                if dot(residual, residual):
                    assert all(dot(residual, w) == 0 for w in orthogonal)
                    orthogonal.append(residual)
            total = Fraction(0)
            for j in range(dimension):
                e = [Fraction(i == j) for i in range(dimension)]
                projection = [Fraction(0) for _ in range(dimension)]
                for w in orthogonal:
                    coefficient = dot(e, w) / dot(w, w)
                    projection = [a + coefficient * b for a, b in zip(projection, w)]
                residual = [a - b for a, b in zip(e, projection)]
                assert all(dot(residual, w) == 0 for w in orthogonal)
                total += dot(residual, residual)
            assert total == dimension - len(orthogonal) >= 1
            checks += 1
    print(f"Rational projection/rank-defect checks: {checks}")


def test_spec_unchanged():
    path = Path(__file__).with_name("Spec.lean")
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    assert digest == SPEC_HASH
    print("Spec.lean unchanged, SHA-256:", digest)


def main():
    test_crt_and_cyclotomic()
    test_factorial_block()
    test_projective()
    test_affine_finite_model()
    test_rank_projection()
    test_spec_unchanged()
    print("PASS: all finite exact checks. No claim of an all-scale cancellation proof.")


if __name__ == "__main__":
    main()
