#!/usr/bin/env python3
"""Finite checks for SubsetProductStudy.md; not a proof of Erdős 1057.

Uses only the Python standard library. The infinite-family arguments are
proved in the note, and their no-zero-sum core is checked independently by Lean.
"""
from collections import Counter
from cmath import exp as cexp
from itertools import combinations
from math import comb, exp, gcd, isqrt, log, pi, prod
from random import Random


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def inverse_pair_check():
    checked = 0
    for modulus in range(1, 251):
        ds = divisors(modulus)
        for k in range(1, 41):
            if gcd(k, modulus) != 1:
                continue
            for d in ds:
                for e in ds:
                    checked += 1
                    if ((k * d + 1) * (k * e + 1) - 1) % modulus == 0:
                        assert d == e, (k, modulus, d, e)
    return checked


def count_by_length_and_residue(values, modulus, max_length):
    """Exact integer DP: each indexed element may be selected at most once."""
    dp = [[0] * modulus for _ in range(max_length + 1)]
    dp[0][0] = 1
    for used, value in enumerate(values):
        for size in range(min(max_length, used + 1), 0, -1):
            for residue, number in enumerate(dp[size - 1]):
                if number:
                    dp[size][(residue + value) % modulus] += number
    return dp


def diagonal_strip_check(ell, h):
    assert is_prime(ell) and 1 <= h < ell
    points = [(x, y) for x in range(ell) for y in range(ell)
              if 1 <= (x + y) % ell <= h]
    n = ell * h
    assert len(points) == n and len(set(points)) == n
    assert set(Counter(x for x, _ in points).values()) == {h}
    assert set(Counter(y for _, y in points).values()) == {h}
    # In F_ell^2, proper nontrivial subgroup cosets are affine lines.
    for u in range(ell):
        for v in range(ell):
            if u == v == 0:
                continue
            counts = Counter((u*x + v*y) % ell for x, y in points)
            assert max(counts.values()) <= ell  # fraction at most 1/h
    limit = (ell - 1) // h
    projected_values = [(x + y) % ell for x, y in points]
    dp = count_by_length_and_residue(projected_values, ell, limit)
    for size in range(1, limit + 1):
        assert dp[size][0] == 0
        assert sum(dp[size]) == comb(n, size)
    return n, limit


def crt_interval_check(r):
    primes = [p for p in range(r*r, 2*r*r) if is_prime(p)][:r]
    assert len(primes) == r
    n = 2 ** r
    modulus = prod(primes)
    assert n*n < modulus
    # For any joint coordinate modulus R, counts differ by at most one.
    # Total variation from uniform is b*(R-b)/(n*R) <= R/(4*n),
    # where n = a*R + b. This identity also applies when n < R.
    max_two_tv = 0.0
    for p, q in combinations(primes, 2):
        joint_modulus = p*q
        a, b = divmod(n, joint_modulus)
        assert a*joint_modulus + b == n
        tv = b*(joint_modulus-b)/(n*joint_modulus)
        assert tv <= joint_modulus/(4*n) + 1e-15
        max_two_tv = max(max_two_tv, tv)
    # Exhaust the nonempty subsets in a separate small CRT example.
    small_modulus, small_n = 5*7*11, 8
    for mask in range(1, 1 << small_n):
        total = sum(i + 1 for i in range(small_n) if mask & (1 << i))
        assert 0 < total < small_modulus and total % small_modulus != 0
    return n, modulus, primes[0], primes[-1], max_two_tv


def support_injective_check(r):
    """Sample the refined divisor-signature construction, not actual primes kd+1."""
    primes = [p for p in range(r*r, 2*r*r) if is_prime(p)][:r]
    assert len(primes) == r
    s = isqrt(r)
    n = comb(r, s)
    modulus = prod(primes)
    height = isqrt(modulus)
    assert n*height < modulus
    rng = Random(1057 + r)
    signatures, values = set(), set()
    marginals = [[0]*p for p in primes]
    total, generated_gcd = 0, modulus
    for support in combinations(range(r), s):
        b = prod(primes[j] for j in support)
        limit = height//b
        assert limit > 0
        while True:
            u = rng.randrange(1, limit+1)
            if gcd(u, modulus//b) == 1:
                break
        a = b*u
        assert 0 < a <= height and gcd(a, modulus) == b
        signatures.add(b)
        values.add(a)
        total += a
        generated_gcd = gcd(generated_gcd, a)
        for j, p in enumerate(primes):
            marginals[j][a % p] += 1
    assert len(signatures) == len(values) == n
    assert 0 < total < modulus and generated_gcd == 1
    zero_count = comb(r-1, s-1)
    assert all(counts[0] == zero_count for counts in marginals)
    max_tv = max(sum(abs(count/n - 1/p) for count in counts)/2
                 for p, counts in zip(primes, marginals))
    return s, n, max_tv


def squarefree_units_embedding_check():
    # Orders are exactly 101, since 101 is prime and these are not the identity.
    ell = 101
    q1, q2 = 607, 809
    b1, b2 = 122, 89
    assert all(map(is_prime, [ell, q1, q2]))
    assert b1 != 1 and b2 != 1
    assert pow(b1, ell, q1) == pow(b2, ell, q2) == 1
    modulus = q1*q2
    points = [(x, y) for x in range(ell) for y in range(ell)
              if 1 <= (x + y) % ell <= 10]
    residues = []
    for x, y in points:
        a1, a2 = pow(b1, x, q1), pow(b2, y, q2)
        z = (a1 + q1 * (((a2-a1)*pow(q1, -1, q2)) % q2)) % modulus
        assert z % q1 == a1 and z % q2 == a2 and gcd(z, modulus) == 1
        residues.append(z)
    assert len(residues) == len(set(residues)) == 1010
    return modulus, len(residues)


def fourier_bound_check():
    """Numerical sanity checks against exact DP counts, not analytic proofs."""
    rng = Random(1057)
    cases = nonvacuous = 0
    for modulus in [2, 3, 5, 7, 11]:
        for repeat in [4, 12, 30]:
            n = modulus * repeat
            pools = [list(range(modulus)) * repeat,
                     [rng.randrange(modulus) for _ in range(n)]]
            for values in pools:
                means = [abs(sum(cexp(2j*pi*j*a/modulus) for a in values)/n)
                         for j in range(1, modulus)]
                delta = max(0.0, 1.0 - max(means))
                lengths = sorted({1, n//4, n//2})
                dp = count_by_length_and_residue(values, modulus, max(lengths))
                for t in lengths:
                    cases += 1
                    assert sum(dp[t]) == comb(n, t)
                    loss = (modulus-1)*(n+1)*exp(-delta*t*(1-t/n))
                    normalized_count = modulus * dp[t][0] / comb(n, t)
                    assert normalized_count + 1e-11 >= 1-loss
                    if loss <= 0.5:
                        nonvacuous += 1
                        assert 2*modulus*dp[t][0] >= comb(n, t)
    assert nonvacuous > 0
    return cases, nonvacuous


def main():
    print('inverse-pair ordered-divisor tests:', inverse_pair_check())
    for ell, h in [(5, 2), (7, 2), (11, 3), (17, 4), (31, 5), (101, 10)]:
        n, limit = diagonal_strip_check(ell, h)
        print(f'strip ell={ell}, h={h}: N={n}; zero subsets of sizes 1..{limit}')
    for r in [10, 20, 40]:
        n, modulus, lo, hi, tv = crt_interval_check(r)
        print(f'CRT r={r}: N={n}, component orders={lo}..{hi}, '
              f'log|G|={log(modulus):.6f}, N^2<|G|, max 2-coordinate TV={tv:.9g}')
    for r in [12, 20, 30]:
        s, n, tv = support_injective_check(r)
        print(f'support-injective r={r}, s={s}, N={n}: sum(A)<|G|, '
              f'generates G, max 1-coordinate TV={tv:.9g}')
    print('squarefree unit-group embedding (modulus, size):',
          squarefree_units_embedding_check())
    print('Fourier bound tests (all, nonvacuous):', fourier_bound_check())
    print('All finite checks passed. No asymptotic claim follows from these tests alone.')


if __name__ == '__main__':
    main()
