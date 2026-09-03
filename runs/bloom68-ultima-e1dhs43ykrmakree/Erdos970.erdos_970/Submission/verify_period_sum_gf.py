#!/usr/bin/env python3
"""Exact certificates for PeriodSumGFReport.md; no parameter search.

Only Python's standard library is used.  Polynomial coefficient lists are in
ascending order.  General statements in the report have mathematical proofs;
this script independently checks the fixed distinct-prime obstruction and the
identities at specified lengths.  It does not prove the period-sum conjecture.
"""

from collections import Counter
from fractions import Fraction
from hashlib import sha256
from math import gcd, prod
from pathlib import Path


def trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a or [0]


def add(a, b, sign=1):
    out = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        out[i] += x
    for i, x in enumerate(b):
        out[i] += sign * x
    return trim(out)


def mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return trim(out)


def shift(a, n):
    return trim([0] * n + list(a))


def divmod_monic(a, b):
    """Integer long division by a monic integer polynomial."""
    assert b[-1] == 1
    rem = trim(a)
    quotient = [0] * max(1, len(rem) - len(b) + 1)
    while rem != [0] and len(rem) >= len(b):
        d = len(rem) - len(b)
        c = rem[-1]
        quotient[d] = c
        for i, x in enumerate(b):
            rem[d + i] -= c * x
        rem = trim(rem)
    return trim(quotient), rem


def q_poly(primes):
    q = [1]
    for p in primes:
        q = mul(q, [1] * p)
    return q


def p_poly(primes, residues):
    q = q_poly(primes)
    p_num = [-x for x in q]
    for p, a in zip(primes, residues):
        assert 0 <= a < p
        p_num = add(p_num, shift(q_poly([r for r in primes if r != p]), a))
    return trim(p_num)


def excess(t, primes, residues):
    return sum(t % p == a for p, a in zip(primes, residues)) - 1


def cyclotomic_divisors(n):
    """Compute Phi_d for each d|n by exact monic division."""
    phis = {}
    for d in range(1, n + 1):
        if n % d:
            continue
        poly = [-1] + [0] * (d - 1) + [1]
        for e, phi in phis.items():
            if d % e == 0:
                poly, remainder = divmod_monic(poly, phi)
                assert remainder == [0]
        phis[d] = poly
    return phis


def main():
    spec = Path(__file__).with_name("Spec.lean")
    expected_spec_hash = (
        "c961aa894dc05a671003b74cd770bf0efc120992bcaaa79466c418b03e1688e7"
    )
    assert sha256(spec.read_bytes()).hexdigest() == expected_spec_hash

    primes = (2, 3, 5, 7)
    residues = (0, 0, 4, 6)
    n = prod(primes)
    d = sum(p - 1 for p in primes)
    sigma = sum((Fraction(1, p) for p in primes), Fraction(0))
    c = n * (sigma - 1)
    assert (n, d, c) == (210, 13, 37)
    assert all(all(p % r for r in range(2, p)) for p in primes)
    assert len(set(primes)) == len(primes)

    q = q_poly(primes)
    p_num = p_poly(primes, residues)
    assert q == [1, 4, 9, 15, 21, 26, 29, 29, 26, 21, 15, 9, 4, 1]
    assert p_num == [1, 2, 2, 1, 1, 1, 2, 3, 4, 5, 6, 5, 3, 1]
    assert all(x > 0 for x in q)
    assert all(x > 0 for x in p_num)
    assert sum(q) == n and sum(p_num) == c
    assert all(174 % p == a for p, a in zip(primes, residues))

    f = [excess(t, primes, residues) for t in range(n)]
    assert f[0] == 1 and f[1] == -1
    assert min(f) == -1 and max(f) == 3
    assert Counter(f) == Counter({-1: 48, 0: 92, 1: 56, 2: 13, 3: 1})
    assert sum(f) == c

    # The Q kernel is exactly uniform modulo every prime.
    for p in primes:
        weights = [sum(q[r::p]) for r in range(p)]
        assert weights == [n // p] * p

    # One complete period certifies the two-sided convolution plateau.
    for t in range(n):
        assert sum(q[j] * excess(t - j, primes, residues)
                   for j in range(d + 1)) == c

    # Fixed lengths verify the general truncation and end-strip formulas.
    lengths = (1, 7, 13, 14, 30, 209, 210, 211, 219, 420, 630)
    for length in lengths:
        b = tuple((a - length) % p for p, a in zip(primes, residues))
        p_b = p_poly(primes, b)
        a_l = [excess(t, primes, residues) for t in range(length)]
        h_l = mul(q, a_l)
        assert mul([1, -1], h_l) == add(p_num, shift(p_b, length), -1)
        exact_counts = [(length + bp - ap) // p for p, ap, bp in
                        zip(primes, residues, b)]
        assert all((length + bp - ap) % p == 0 for p, ap, bp in
                   zip(primes, residues, b))
        assert sum(a_l) == sum(exact_counts) - length
        assert sum(a_l) == length * (sigma - 1) + sum(
            (Fraction(bp - ap, p) for p, ap, bp in zip(primes, residues, b)),
            Fraction(0))
        if length > d:
            padded_h = h_l + [0] * (length + d - len(h_l))
            c_a = [sum(p_num[:r + 1]) for r in range(d)]
            c_b = [sum(p_b[:r + 1]) for r in range(d)]
            expected_h = c_a + [int(c)] * (length - d) + [int(c) - x for x in c_b]
            assert padded_h == expected_h
        if length % n == 0:
            assert b == residues
            assert h_l == mul(p_num, [1] * length)
            assert min(h_l) > 0
            assert min(a_l) == -1
            quotient, remainder = divmod_monic(h_l, q)
            assert remainder == [0] and quotient == trim(a_l)
            print(f"L={length}: H_L>0 coefficientwise, Q|H_L, "
                  f"but min(H_L/Q)=-1; {a_l.count(-1)} uncovered positions")

    # The cleared test even passes at the proposed bound D+1=14.
    assert min(mul(q, [excess(t, primes, residues) for t in range(d + 1)])) >= 0

    # All pole orders for the genuine excess and genuine hole indicator.
    phis = cyclotomic_divisors(n)
    holes = [int(x == -1) for x in f]
    excess_orders = []
    hole_orders = []
    for order, phi in phis.items():
        if divmod_monic(f, phi)[1] != [0]:
            excess_orders.append(order)
        if divmod_monic(holes, phi)[1] != [0]:
            hole_orders.append(order)
    assert excess_orders == [1, 2, 3, 5, 7]
    assert sum(len(phis[o]) - 1 for o in excess_orders) == d + 1
    assert hole_orders == list(phis)
    assert sum(len(phi) - 1 for phi in phis.values()) == n

    # A separate recurrence/Fine-Wilf obstruction, NOT a one-class cover.
    complement_residues = tuple(p - 1 for p in primes)
    complement_f = [len(primes) - 1 - sum(t % p == a for p, a in
                                         zip(primes, complement_residues))
                    for t in range(n)]
    assert min(complement_f[:n - 1]) == 0
    assert complement_f[n - 1] == -1
    assert all(-1 <= x <= len(primes) - 1 for x in complement_f)

    # Compute j(210) only to distinguish our obstruction from a counterexample
    # to the actual period-sum conjecture.  No prime/residue parameter search.
    totatives = [t for t in range(n) if gcd(t, n) == 1]
    cyclic_pairs = list(zip(totatives, totatives[1:] + [totatives[0] + n]))
    jacobsthal = max(b - a for a, b in cyclic_pairs)
    assert jacobsthal == 10 < d + 1
    assert all(gcd(t, n) > 1 for t in range(200, 209))
    assert gcd(199, n) == gcd(209, n) == 1

    # Algebraic lift: adding a fresh prime r gives P_new=P_old*Q_r+Q_old
    # when its residue is zero.  This preserves strict positivity and the hole
    # at t=1.  No full period of the enlarged set is enumerated.
    large_primes = primes
    large_residues = residues
    large_q, large_p = q, p_num
    for r in (11, 13, 17, 19, 23, 29):
        next_q = mul(large_q, [1] * r)
        next_p = add(mul(large_p, [1] * r), large_q)
        large_primes += (r,)
        large_residues += (0,)
        assert next_q == q_poly(large_primes)
        assert next_p == p_poly(large_primes, large_residues)
        assert all(x > 0 for x in next_p)
        assert excess(1, large_primes, large_residues) == -1
        large_q, large_p = next_q, next_p
    large_n = prod(large_primes)
    large_sigma = sum((Fraction(1, p) for p in large_primes), Fraction(0))
    large_c = large_n * (large_sigma - 1)
    assert large_sigma > Fraction(3, 2)
    assert all(large_n // p <= large_c for p in large_primes)
    print(f"Lift to first 10 primes: N={large_n}, D={len(large_q)-1}, "
          f"sigma={large_sigma}>3/2, P>0, f(1)=-1")
    print("For full-period lengths, all Nth-root single-frequency triangle "
          "tests pass (by the exact Fourier formula in the report)")

    print("Q coefficients:", q)
    print("P coefficients:", p_num)
    print("D=13; N=210; sigma=247/210; C=37")
    print("One-period excess histogram:", dict(sorted(Counter(f).items())))
    print("Excess minimal recurrence order: 14; hole-indicator order: 210")
    print("j(210)=10 < 14: this is NOT a period-sum counterexample")
    print("All fixed exact certificates passed; no asymptotic claim was tested")
    print("Spec.lean SHA-256:", expected_spec_hash)


if __name__ == "__main__":
    main()
