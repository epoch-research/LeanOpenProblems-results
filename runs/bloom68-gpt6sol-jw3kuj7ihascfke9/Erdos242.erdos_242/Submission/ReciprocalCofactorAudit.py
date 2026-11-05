#!/usr/bin/env python3
"""Exact finite audit of the reciprocal Type-II test; not a universal proof.

Every v up to the stated cutoff and every m satisfying the exact size
inequality are checked, with no d|m substitution for d|m**2.
"""
from math import isqrt


def is_prime(n):
    if n < 2:
        return False
    return all(n % q for q in range(2, isqrt(n) + 1))


def square_root_divisor(v):
    """Smallest positive rho such that v | rho**2 (full prime exponents)."""
    rho, n, q = 1, v, 2
    while q * q <= n:
        if n % q == 0:
            e = 0
            while n % q == 0:
                e, n = e + 1, n // q
            rho *= q ** ((e + 1) // 2)
        q += 1
    if n > 1:
        rho *= n
    return rho


def reciprocal_witness(p, max_v):
    """Return the first (v,m,d), or None after an EXHAUSTIVE v<=max_v scan.

    4*m*m < v*p iff m <= isqrt((v*p-1)//4); on p=1 mod 24,
    full_square_axis_bound also restricts m <= (p-1)//6.
    """
    assert p > 1 and p % 24 == 1
    for v in range(1, max_v + 1):
        rho = square_root_divisor(v)
        largest = min((p - 1) // 6, isqrt((v * p - 1) // 4))
        F = 4 * v * p + 1
        for m in range(rho, largest + 1, rho):
            h = 4 * m - 1
            if F % h:
                continue
            assert m * m % v == 0
            d = m * m // v
            assert d > 0 and m * m % d == 0 and 4 * d < p
            assert (p + 4 * d) % h == 0 and h % (4 * rho) == 4 * rho - 1
            return v, m, d
    return None


def run():
    # Includes all requested stress primes and the first explicit obstacle to
    # the apparently promising universal v<=64 cofactor shortcut.
    for p, expected in [(73, (2, 4, 8)), (193, (2, 4, 8)),
                        (241, (3, 3, 3)), (2521, (9, 12, 16)),
                        (66529, (2, 10, 50)),
                        (1726201, (144, 5748, 229441))]:
        assert is_prime(p)
        assert reciprocal_witness(p, expected[0] - 1) is None
        assert reciprocal_witness(p, expected[0]) == expected
        v, m, d = expected
        print(f"prime {p}: least cofactor v={v}, witness (m,d)=({m},{d})")

    p = 1726201
    assert reciprocal_witness(p, 64) is None
    # The negative result is only for v<=64: this SAME prime has a much
    # shorter m=60 witness with v=150, showing the two search orders differ.
    m, d = 60, 24
    assert d * 150 == m * m and 4 * d < p
    assert (p + 4 * d) % (4 * m - 1) == 0
    assert (4 * 150 * p + 1) % (4 * m - 1) == 0
    print("prime 1726201: no v<=64 witness; (m,d,v)=(60,24,150) works")

    # Odd-square composites have NO full Type-II witnesses at ANY m by the
    # Jacobi-symbol argument in FullSquareAxis.md. These finite checks only
    # test small m; they do NOT constitute that all-m mathematical proof.
    for s in (5, 7, 11, 1000001):
        n = s * s
        assert n % 24 == 1 and not is_prime(n)
        assert reciprocal_witness(n, 100) is None
        print(f"odd-square composite {n}: no reciprocal witness with v<=100")
    print("PASS: exact finite checks; the universal prime case remains open")


if __name__ == "__main__":
    run()
