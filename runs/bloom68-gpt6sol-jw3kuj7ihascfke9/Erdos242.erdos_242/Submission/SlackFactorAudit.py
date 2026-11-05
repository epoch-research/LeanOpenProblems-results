"""Finite integer-only checks for the positive-A factor criterion.

This verifies ONLY the listed five primes and their stated *minimal* positive
ordered A. It is not a proof of an all-prime A-construction. Run with
`python3 Submission/SlackFactorAudit.py`.
"""

from math import isqrt


def prime_by_trial(p: int) -> bool:
    if p < 2:
        return False
    return all(p % d for d in range(2, isqrt(p) + 1))


def certificates(p: int, A: int):
    """Yield all ordered factor certificates at a specified positive A.

    Divisors a up to sqrt(N) suffice: every a<b with ab=N occurs here.
    All divisions are exact, all arithmetic is with Python integers.
    """
    assert p % 4 == 1 and A > 0
    N = p * p + 4 * A
    for a in range(3, isqrt(N) + 1, 4):
        if N % a:
            continue
        b = N // a
        if b % 4 != 3 or a >= b or a >= p:
            continue
        x, y = (p + a) // 4, (p + b) // 4
        assert (p + a) == 4 * x and (p + b) == 4 * y
        if (x * y) % A != 0 or A >= p * x:
            continue
        z = p * (x * y // A)
        assert x < y < z
        assert (4 * x - p, 4 * y - p) == (a, b)
        assert a * b == N and 4 * x * y == p * (x + y) + A
        assert 4 * x * y * z == p * (x * y + x * z + y * z)
        yield a, b, x, y, z


def main():
    for p, target in [(73, 7), (193, 10), (2521, 76), (66529, 19), (18481, 38)]:
        assert prime_by_trial(p) and p % 24 == 1
        assert all(not list(certificates(p, A)) for A in range(1, target))
        certs = list(certificates(p, target))
        assert certs
        assert (p - 1) % target != 0
        assert pow(target, (p - 1) // 2, p) == p - 1  # nonresidue
        print(f"p={p} minimal A={target}: (a,b,x,y,z)={certs[0]}")

    # A negative Legendre symbol AND eligible 3 (mod 4) factor pairs still
    # do not force the missing integrality condition A | x*y.
    p, A = 193, 5
    assert pow(A, (p - 1) // 2, p) == p - 1
    N = p * p + 4 * A
    candidate_residues = []
    for a in range(3, isqrt(N) + 1, 4):
        if N % a != 0:
            continue
        b = N // a
        if b % 4 != 3 or a >= b or a >= p:
            continue
        x, y = (p + a) // 4, (p + b) // 4
        if A < p * x:
            candidate_residues.append((a, b, (x * y) % A))
    assert candidate_residues == [(3, 12423, 1), (123, 303, 1)]
    print("nonresidue not sufficient: p=193, A=5, xy mod A=1 at both eligible factors")

    # The factor and divisibility conditions alone do NOT impose y<z:
    # 11*12191 = 73^2 + 4*32193, and 32193 | 21*3066.
    p, A, a, b, x, y = 73, 32193, 11, 12191, 21, 3066
    assert a * b == p * p + 4 * A
    assert (p + a, p + b) == (4 * x, 4 * y)
    assert x * y % A == 0
    z = p * (x * y // A)
    assert (x, z, y) == (21, 146, 3066)
    assert not A < p * x
    print("ordering caveat: (x,y,z)=(21,3066,146) at p=73, A=32193")


if __name__ == "__main__":
    main()
